// © 2020, ETH Zurich
//
// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.

use std::collections::HashMap;

use log::info;
use rustc_middle::mir;
use rustc_span;

pub trait MirAnalysis<ResultType> {
    fn run(&mut self);
}

#[derive(Debug, Clone, Eq, PartialEq)]
pub struct MirAnalysisResult<T> {
    pub before_block: HashMap<mir::BasicBlock, T>,
    pub after_block: HashMap<mir::BasicBlock, T>,
    pub before_terminator: HashMap<mir::BasicBlock, T>,
    pub before_statement: HashMap<mir::Location, T>,
    pub after_statement: HashMap<mir::Location, T>,
}

// TODO: Realised too late that the location of the terminatior is a valid location after all, maybe merge before_terminator into before_statement
impl<T> MirAnalysisResult<T> {
    pub fn new() -> Self {
        MirAnalysisResult {
            before_block: HashMap::new(),
            after_block: HashMap::new(),
            before_terminator: HashMap::new(),
            before_statement: HashMap::new(),
            after_statement: HashMap::new(),
        }
    }
}

pub fn closest_result_to<'a, T>(
    mir: &mir::Body,
    result: &'a MirAnalysisResult<T>,
    source_map: &rustc_span::source_map::SourceMap,
    line: usize,
    char_pos: usize,
) -> &'a T {
    let mut nearest = (
        rustc_span::LineInfo {
            line_index: 0,
            start_col: rustc_span::CharPos(0),
            end_col: rustc_span::CharPos(0),
        },
        mir::Location {
            block: mir::BasicBlock::from_u32(0),
            statement_index: 0,
        },
        None,
    );

    //let mut outp = None;
    for bb in mir.basic_blocks().indices() {
        let mir::BasicBlockData {
            ref statements,
            ref terminator,
            ..
        } = mir[bb];

        for statement_index in 0..statements.len() {
            let location = mir::Location {
                block: bb,
                statement_index,
            };

            if let Ok(file_lines) = source_map.span_to_lines(mir.source_info(location).span) {
                if file_lines
                    .lines
                    .iter()
                    .all(|line_info| line_info.line_index <= line)
                    && file_lines
                        .lines
                        .iter()
                        .find(|line_info| {
                            line_info.line_index == line
                                && line_info.start_col.0 <= char_pos
                                && line_info.end_col.0 >= char_pos
                        })
                        .is_some()
                {
                    info!(
                        "We think: {:?} is a perfect match for {}:{} ({:?})",
                        source_map
                            .span_to_lines(mir.source_info(location).span)
                            .unwrap()
                            .lines,
                        line,
                        char_pos,
                        location
                    );
                    return result.after_statement.get(&location).unwrap();
                }

                let max_line = file_lines.lines.iter().fold_first(|cur_max, line_info| {
                    if line_info.line_index > cur_max.line_index
                        || (line_info.line_index == cur_max.line_index
                            && line_info.end_col.0 > cur_max.end_col.0)
                    {
                        line_info
                    } else {
                        cur_max
                    }
                });
                if file_lines
                    .lines
                    .iter()
                    .all(|line_info| line_info.line_index <= line)
                    && max_line.map_or(false, |line_info| {
                        line_info.line_index > nearest.0.line_index
                            || (line_info.line_index == nearest.0.line_index
                                && line_info.end_col.0 > nearest.0.end_col.0)
                    })
                {
                    nearest.0 = max_line.unwrap().clone();
                    nearest.1 = location.clone();
                    nearest.2 = result.after_statement.get(&location);
                }
            }
        }

        if let Some(t) = terminator {
            if let Ok(file_lines) = source_map.span_to_lines(t.source_info.span) {
                if file_lines
                    .lines
                    .iter()
                    .all(|line_info| line_info.line_index <= line)
                    && file_lines
                        .lines
                        .iter()
                        .find(|line_info| {
                            line_info.line_index == line
                                && line_info.start_col.0 <= char_pos
                                && line_info.end_col.0 >= char_pos
                        })
                        .is_some()
                {
                    info!(
                        "We think: {:?} is a perfect match for {}:{} (terminator of {:?})",
                        source_map.span_to_lines(t.source_info.span).unwrap().lines,
                        line,
                        char_pos,
                        bb
                    );
                    return result.after_block.get(&bb).unwrap();
                }

                let max_line = file_lines.lines.iter().fold_first(|cur_max, line_info| {
                    if line_info.line_index > cur_max.line_index
                        || (line_info.line_index == cur_max.line_index
                            && line_info.end_col.0 > cur_max.end_col.0)
                    {
                        line_info
                    } else {
                        cur_max
                    }
                });
                if file_lines
                    .lines
                    .iter()
                    .all(|line_info| line_info.line_index <= line)
                    && max_line.map_or(false, |line_info| {
                        line_info.line_index > nearest.0.line_index
                            || (line_info.line_index == nearest.0.line_index
                                && line_info.end_col.0 > nearest.0.end_col.0)
                    })
                {
                    nearest.0 = max_line.unwrap().clone();
                    nearest.1 = mir::Location {
                        block: bb,
                        statement_index: statements.len(),
                    }
                    .clone();
                    nearest.2 = result.after_block.get(&bb);
                }
            }
        }
    }

    if let (file_line, location, Some(result)) = nearest {
        info!(
            "Closest to line {}:{} was {:?} (MIR location: {:?})",
            line, char_pos, file_line, location
        );
        result
    } else {
        result
            .after_block
            .get(&mir.basic_blocks().indices().last().unwrap())
            .unwrap()
    }
}

pub enum WorkItem {
    /// Need to apply the effects of the statement.
    ApplyStatementEffects(mir::Location),
    /// Need to apply the effects of the terminator.
    ApplyTerminatorEffects(mir::BasicBlock),
    /// Need to merge the incoming effects of multiple edges.
    MergeEffects(mir::BasicBlock),
}

pub fn print_mir_result<T: std::fmt::Display>(mir: &mir::Body, result: &MirAnalysisResult<T>) {
    for bb in mir.basic_blocks().indices() {
        println!("{:?} {{", bb);
        let mir::BasicBlockData {
            ref statements,
            ref terminator,
            ..
        } = mir[bb];
        println!("{}", result.before_block[&bb]);

        for statement_index in 0..statements.len() {
            let location = mir::Location {
                block: bb,
                statement_index,
            };

            let statement = mir[location.block].statements[location.statement_index].clone();
            match statement.kind.clone() {
                mir::StatementKind::Assign(_) | mir::StatementKind::SetDiscriminant { .. } => (),
                _ => continue,
            };

            println!("\n    {}", result.before_statement[&location]);
            println!("    {:?} //{:?}[{}]", statement, bb, statement_index);
            println!("    {:?}", statement.source_info);
            println!("    {}\n", result.after_statement[&location]);
        }
        if let Some(t) = terminator {
            println!("    {:?} // terminator\n", t.kind);
            println!("    {:?}", t.source_info);
        }
        println!("{}", result.after_block[&bb]);
        println!("}}\n")
    }
}

pub fn print_mir_graphviz<T: std::fmt::Display>(mir: &mir::Body, result: &MirAnalysisResult<T>) {
    let mut relations = Vec::new();
    println!("digraph G {{");

    println!("labelloc=\"t\";");

    let mut var_symbols = Vec::new();
    for info in mir.var_debug_info.iter() {
        var_symbols.push(format!(
            "<tr><td>{:?}</td><td>{:?}</td></tr>",
            info.place, info.name
        ));
    }
    println!(
        "label=<<table><tr><td>Local</td><td>Symbol</td></tr>{}</table>>;",
        var_symbols.join("\n")
    );

    for bb in mir.basic_blocks().indices() {
        let mir::BasicBlockData {
            ref statements,
            ref terminator,
            ..
        } = mir[bb];

        let pcs_before_block = escape_html(format!("{}", result.before_block[&bb]));
        let mut label = vec![format!(
            "<table><tr><td><font color=\"tomato\">{}</font></td></tr>",
            pcs_before_block
        )];

        for statement_index in 0..statements.len() {
            let location = mir::Location {
                block: bb,
                statement_index,
            };

            let statement = mir[location.block].statements[location.statement_index].clone();
            match statement.kind.clone() {
                mir::StatementKind::Assign(_) | mir::StatementKind::SetDiscriminant { .. } => (),
                _ => continue,
            };

            let pcs_before_statement =
                escape_html(format!("{}", result.before_statement[&location]));
            label.push(format!(
                "<tr><td><table><tr><td><font color=\"forestgreen\">{}</font></td></tr>",
                pcs_before_statement
            ));

            let statement_string =
                escape_html(format!("{:?}[{}]:  {:?}", bb, statement_index, statement));
            label.push(format!("<tr><td>{}</td></tr>", statement_string));

            let pcs_after_statement = escape_html(format!("{}", result.after_statement[&location]));
            label.push(format!(
                "<tr><td><font color=\"royalblue\">{}</font></td></tr></table></td></tr>",
                pcs_after_statement
            ));
        }
        if let Some(t) = terminator {
            let pcs_before_terminator = escape_html(format!("{}", result.before_terminator[&bb]));
            label.push(format!(
                "<tr><td><font color=\"forestgreen\">{}</font></td></tr>",
                pcs_before_terminator
            ));

            let terminator_string = escape_html(format!("{:?}", t.kind));
            label.push(format!("<tr><td>{}</td></tr>", terminator_string));
        }

        let pcs_after_block = escape_html(format!("{}", result.after_block[&bb]));
        label.push(format!(
            "<tr><td><font color=\"tomato\">{}</font></td></tr></table>",
            pcs_after_block
        ));

        println!(
            "block{} [shape=plain, xlabel=\"bb{}\" label=<{}>];",
            bb.as_usize(),
            bb.as_usize(),
            label.join("\n")
        );
        for predecessor in mir.predecessors()[bb].clone() {
            relations.push(format!(
                "block{} -> block{};",
                predecessor.as_u32(),
                bb.as_u32()
            ));
        }
    }

    println!("{}", relations.join("\n"));

    println!("}}");
}

fn escape_html(to_escape: String) -> String {
    to_escape
        .replace("&", "&amp;")
        .replace("<", "&lt;")
        .replace(">", "&gt;")
}
