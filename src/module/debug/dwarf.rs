//! transform entries in WebAssembly DWARF sections

/// `write` provides only address-based entry conversions,
/// does not provide entry-wise conversions.
/// We want to convert addresses of instructions, here will re-implement.
use gimli::*;

use super::units::DebuggingInformationCursor;

#[derive(Debug, PartialEq)]
pub enum AddressSearchPreference {
    /// Normal range comparison (inclusive start, exclusive end)
    ExclusiveFunctionEnd,
    /// Prefer treating a beginning point as the ending point of the previous function.
    InclusiveFunctionEnd,
}

pub(crate) static DEAD_CODE: u64 = 0xFFFFFFFF;

/// DWARF convertion context
pub(crate) struct ConvertContext<'a, R: Reader<Offset = usize>> {
    /// Source DWARF debug data
    pub dwarf: &'a read::Dwarf<R>,

    pub strings: &'a mut write::StringTable,
    pub line_strings: &'a mut write::LineStringTable,

    /// Address conversion function.
    /// First argument is an address in original wasm binary.
    /// If the address is mapped in transformed wasm binary, the address should be wrapped in Option::Some.
    /// If the address is not mapped, None should be returned.
    pub convert_address: &'a dyn Fn(u64, AddressSearchPreference) -> Option<write::Address>,
}

impl<'a, R> ConvertContext<'a, R>
where
    R: Reader<Offset = usize>,
{
    pub(crate) fn new(
        dwarf: &'a read::Dwarf<R>,
        strings: &'a mut write::StringTable,
        line_strings: &'a mut write::LineStringTable,
        convert_address: &'a dyn Fn(u64, AddressSearchPreference) -> Option<write::Address>,
    ) -> Self {
        ConvertContext {
            dwarf,
            strings,
            line_strings,
            convert_address,
        }
    }

    pub(crate) fn convert_high_pc(
        &self,
        from_unit: &mut gimli::read::EntriesCursor<R>,
        unit: &mut DebuggingInformationCursor,
    ) {
        while let (Ok(Some((_, from_debug_entry))), Some(debug_entry)) =
            (from_unit.next_dfs(), unit.next_dfs())
        {
            let low_pc = from_debug_entry
                .attr_value(constants::DW_AT_low_pc)
                .expect("low_pc");
            let high_pc = from_debug_entry
                .attr_value(constants::DW_AT_high_pc)
                .expect("high_pc");

            if let (Some(AttributeValue::Addr(low_addr)), Some(AttributeValue::Udata(offset))) =
                (low_pc, high_pc)
            {
                let new_low_pc =
                    (self.convert_address)(low_addr, AddressSearchPreference::InclusiveFunctionEnd);
                let new_high_pc = (self.convert_address)(
                    low_addr + offset,
                    AddressSearchPreference::InclusiveFunctionEnd,
                );
                if let (
                    Some(write::Address::Constant(new_low_pc)),
                    Some(write::Address::Constant(new_high_pc)),
                ) = (new_low_pc, new_high_pc)
                {
                    debug_entry.set(
                        constants::DW_AT_high_pc,
                        write::AttributeValue::Udata(new_high_pc.saturating_sub(new_low_pc)),
                    );
                }
            }
        }
    }

    pub(crate) fn convert_unit_line_program(
        &mut self,
        from_unit: read::Unit<R>,
    ) -> Option<write::LineProgram> {
        let from_program = from_unit.line_program.clone()?;
        let line_program = self
            .convert_line_program(from_program, from_unit.name.clone())
            .expect("cannot convert line program");
        Some(line_program)
    }

    /// Perform address conversion in DWARF line program entries.
    fn convert_line_program(
        &mut self,
        from_program: read::IncompleteLineProgram<R>,
        comp_name: Option<R>,
    ) -> write::ConvertResult<write::LineProgram> {
        let encoding = from_program.header().encoding();
        let line_encoding = from_program.header().line_encoding();
        let mut convert = write::LineConvert::new(
            self.dwarf,
            from_program,
            comp_name,
            encoding,
            line_encoding,
            self.line_strings,
            self.strings,
        )?;

        while let Some(sequence) = convert.read_sequence()? {
            // begin new sequence if exists
            let Some(from_start) = sequence.start else {
                continue;
            };
            let Some(write::Address::Constant(start)) =
                (self.convert_address)(from_start, AddressSearchPreference::ExclusiveFunctionEnd)
            else {
                continue;
            };
            let Some(write::Address::Constant(end)) = (self.convert_address)(
                from_start + sequence.length,
                AddressSearchPreference::InclusiveFunctionEnd,
            ) else {
                continue;
            };
            convert.begin_sequence(Some(write::Address::Constant(start)));
            for mut row in sequence.rows {
                let Some(write::Address::Constant(address)) = (self.convert_address)(
                    from_start + row.address_offset,
                    AddressSearchPreference::InclusiveFunctionEnd,
                ) else {
                    continue;
                };
                row.address_offset = address - start;
                convert.generate_row(row);
            }
            convert.end_sequence(end - start);
        }
        Ok(convert.program().0)
    }
}

#[cfg(test)]
mod tests {
    use crate::module::debug::units::DebuggingInformationCursor;

    use super::AddressSearchPreference;
    use gimli::*;
    use std::cell::RefCell;

    fn make_test_debug_line<'a>(
        debug_line: &'a mut write::DebugLine<write::EndianVec<LittleEndian>>,
    ) -> IncompleteLineProgram<EndianSlice<'a, LittleEndian>> {
        let encoding = Encoding {
            format: Format::Dwarf32,
            version: 4,
            address_size: 4,
        };
        let dir1 = &b"dir1"[..];
        let file1 = &b"file1"[..];
        let comp_file = write::LineString::String(file1.to_vec());

        let mut program = write::LineProgram::new(
            encoding,
            LineEncoding {
                minimum_instruction_length: 1,
                maximum_operations_per_instruction: 8,
                line_base: 0,
                line_range: 10,
                default_is_stmt: true,
            },
            write::LineString::String(dir1.to_vec()),
            comp_file.clone(),
            None,
        );

        {
            program.row().file = program.add_file(comp_file, program.default_directory(), None);
            program.begin_sequence(Some(write::Address::Constant(0x1000)));
            program.generate_row();
            let address_offset = program.row().address_offset + 1u64;
            program.end_sequence(address_offset);
        }

        program
            .write(
                debug_line,
                encoding,
                &write::DebugLineStrOffsets::none(),
                &write::DebugStrOffsets::none(),
            )
            .unwrap();

        let debug_line = read::DebugLine::new(debug_line.slice(), LittleEndian);
        let incomplete_debug_line = debug_line
            .program(DebugLineOffset(0), 4, None, None)
            .unwrap();

        incomplete_debug_line
    }

    #[test]
    fn convert_callback_invoke() {
        let called_address_to_be_converted: RefCell<Vec<(u64, AddressSearchPreference)>> =
            RefCell::new(Vec::new());
        {
            let mut debug_line = write::DebugLine::from(write::EndianVec::new(LittleEndian));
            let incomplete_debug_line = make_test_debug_line(&mut debug_line);

            let convert_address = |address, preference| -> Option<write::Address> {
                called_address_to_be_converted
                    .borrow_mut()
                    .push((address, preference));
                Some(write::Address::Constant(address + 0x10))
            };

            let empty_dwarf = Dwarf::default();

            let mut line_strings = write::LineStringTable::default();
            let mut strings = write::StringTable::default();
            let mut convert_context = crate::module::debug::ConvertContext::new(
                &empty_dwarf,
                &mut strings,
                &mut line_strings,
                &convert_address,
            );
            convert_context
                .convert_line_program(incomplete_debug_line, None)
                .unwrap();
        }

        {
            let called_address_to_be_converted = called_address_to_be_converted.borrow();
            assert_eq!(called_address_to_be_converted.len(), 3);
            assert_eq!(
                called_address_to_be_converted[0],
                (0x1000, AddressSearchPreference::ExclusiveFunctionEnd)
            ); // begin sequence
            assert_eq!(
                called_address_to_be_converted[2],
                (0x1000, AddressSearchPreference::InclusiveFunctionEnd)
            ); // first line row
            assert_eq!(
                called_address_to_be_converted[1],
                (0x1001, AddressSearchPreference::InclusiveFunctionEnd)
            ); // end sequence
        }
    }

    #[test]
    fn test_converted_address() {
        let mut converted_debug_line = write::DebugLine::from(write::EndianVec::new(LittleEndian));
        {
            let mut debug_line = write::DebugLine::from(write::EndianVec::new(LittleEndian));
            let incomplete_debug_line = make_test_debug_line(&mut debug_line);

            let convert_address = |address, _| -> Option<write::Address> {
                Some(write::Address::Constant(address + 0x10))
            };

            let empty_dwarf = Dwarf::default();
            let mut line_strings = write::LineStringTable::default();
            let mut strings = write::StringTable::default();

            let mut convert_context = crate::module::debug::ConvertContext::new(
                &empty_dwarf,
                &mut strings,
                &mut line_strings,
                &convert_address,
            );
            let converted_program = convert_context
                .convert_line_program(incomplete_debug_line, None)
                .unwrap();

            converted_program
                .write(
                    &mut converted_debug_line,
                    converted_program.encoding(),
                    &write::DebugLineStrOffsets::none(),
                    &write::DebugStrOffsets::none(),
                )
                .unwrap();
        }

        {
            let read_debug_line = read::DebugLine::new(converted_debug_line.slice(), LittleEndian);
            let read_program = read_debug_line
                .program(DebugLineOffset(0), 4, None, None)
                .unwrap();

            let mut rows = read_program.rows();
            let row = rows.next_row().unwrap().unwrap().1;
            assert_eq!(row.address(), 0x1010);
        }
    }

    #[test]
    fn test_converted_none_address() {
        let mut converted_debug_line = write::DebugLine::from(write::EndianVec::new(LittleEndian));
        {
            let mut debug_line = write::DebugLine::from(write::EndianVec::new(LittleEndian));
            let incomplete_debug_line = make_test_debug_line(&mut debug_line);

            let convert_address = |_, _| -> Option<write::Address> { None };

            let empty_dwarf = Dwarf::default();
            let mut line_strings = write::LineStringTable::default();
            let mut strings = write::StringTable::default();

            let mut convert_context = crate::module::debug::ConvertContext::new(
                &empty_dwarf,
                &mut strings,
                &mut line_strings,
                &convert_address,
            );
            let converted_program = convert_context
                .convert_line_program(incomplete_debug_line, None)
                .unwrap();

            converted_program
                .write(
                    &mut converted_debug_line,
                    converted_program.encoding(),
                    &write::DebugLineStrOffsets::none(),
                    &write::DebugStrOffsets::none(),
                )
                .unwrap();
        }

        {
            let read_debug_line = read::DebugLine::new(converted_debug_line.slice(), LittleEndian);
            let read_program = read_debug_line
                .program(DebugLineOffset(0), 4, None, None)
                .unwrap();

            let mut rows = read_program.rows();
            let row = rows.next_row().unwrap();
            assert!(row.is_none());
        }
    }

    fn make_test_debug_info() -> write::Sections<write::EndianVec<LittleEndian>> {
        let mut unit_table = write::UnitTable::default();
        {
            let mut unit1 = write::Unit::new(
                Encoding {
                    version: 4,
                    address_size: 4,
                    format: Format::Dwarf32,
                },
                write::LineProgram::none(),
            );

            let root_id = unit1.root();
            let child1_id = unit1.add(root_id, constants::DW_TAG_subprogram);
            unit1.get_mut(child1_id).set(
                constants::DW_AT_low_pc,
                write::AttributeValue::Address(write::Address::Constant(0x1000)),
            );
            unit1.get_mut(child1_id).set(
                constants::DW_AT_high_pc,
                write::AttributeValue::Udata(0x100),
            );

            unit_table.add(unit1);
        }

        let mut sections = write::Sections::new(write::EndianVec::new(LittleEndian));
        unit_table
            .write(
                &mut sections,
                &write::DebugLineStrOffsets::none(),
                &write::DebugStrOffsets::none(),
            )
            .unwrap();
        sections
    }

    #[test]
    fn test_convert_high_pc() {
        let sections = make_test_debug_info();
        let mut read_dwarf = Dwarf::default();

        read_dwarf.debug_info = read::DebugInfo::new(sections.debug_info.slice(), LittleEndian);
        read_dwarf.debug_abbrev =
            read::DebugAbbrev::new(sections.debug_abbrev.slice(), LittleEndian);

        let read_first_unit_header = read_dwarf.units().next().unwrap().unwrap();
        let read_first_unit = read_dwarf.unit(read_first_unit_header).unwrap();
        let mut read_first_unit_entries = read_first_unit.entries();

        let convert_address = |address, _| -> Option<write::Address> {
            if address < 0x1050 {
                Some(write::Address::Constant(address + 0x10))
            } else {
                Some(write::Address::Constant(address - 0x10))
            }
        };

        let mut strings = write::StringTable::default();
        let mut line_strings = write::LineStringTable::default();

        let convert_context = crate::module::debug::ConvertContext::new(
            &read_dwarf,
            &mut strings,
            &mut line_strings,
            &convert_address,
        );

        let mut converted_dwarf = write::Dwarf::from(&read_dwarf, &|address| {
            convert_address(address, AddressSearchPreference::InclusiveFunctionEnd)
        })
        .unwrap();

        let id = converted_dwarf.units.id(0);

        {
            let unit = converted_dwarf.units.get_mut(id);
            let mut write_unit_first_entries = DebuggingInformationCursor::new(unit);

            convert_context
                .convert_high_pc(&mut read_first_unit_entries, &mut write_unit_first_entries);
        }

        {
            let unit = converted_dwarf.units.get_mut(id);
            let mut write_unit_first_entries = DebuggingInformationCursor::new(unit);

            let _root = write_unit_first_entries.next_dfs();
            let subprogram_entry = write_unit_first_entries.next_dfs().unwrap();

            assert_eq!(
                *subprogram_entry.get(DW_AT_low_pc).unwrap(),
                write::AttributeValue::Address(write::Address::Constant(0x1010))
            );
            assert_eq!(
                *subprogram_entry.get(DW_AT_high_pc).unwrap(),
                write::AttributeValue::Udata(0xE0)
            );
        }
    }
}
