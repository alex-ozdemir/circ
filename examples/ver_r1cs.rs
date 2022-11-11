use circ::ir::term::text::*;
use circ::target::r1cs::ver_trans::{
    lang::{OpPattern, SortPat},
    rules::{rules, Enc},
    ver::{
        c_completeness_terms, c_soundness_terms, completeness_terms, soundness_terms,
        v_completeness_terms, v_soundness_terms, Bound,
    },
};
use circ::target::smt::find_model;
use circ::util::field::DFL_T;
use structopt::{clap::arg_enum, StructOpt};

#[derive(Debug, StructOpt)]
#[structopt(name = "ver_r1cs", about = "Verifier for CirC's R1CS lowering pass")]
struct Options {
    #[structopt(long, short = "a")]
    max_args: usize,

    #[structopt(long, short = "b")]
    max_bv_bits: usize,

    #[structopt(long, short)]
    properties: Vec<Prop>,

    #[structopt(long, short)]
    ops: Vec<String>,

    #[structopt(long, short = "O")]
    excluded_ops: Vec<String>,

    #[structopt(long, short)]
    rule_types: Vec<RuleType>,

    #[structopt(long, short, possible_values = &["bool", "bitvector", "field"])]
    sorts: Vec<String>,
}

arg_enum! {
    /// A verifiable property: 'sound' or 'complete'
    #[derive(Debug, PartialEq, Eq, Clone)]
    enum Prop {
        Sound,
        Complete,
    }
}

arg_enum! {
    /// A verifiable property: 'sound' or 'complete'
    #[derive(Debug, PartialEq, Eq, Clone)]
    enum RuleType {
        Var,
        Conv,
        Enc,
    }
}

impl Prop {
    fn failure_message(&self) -> &'static str {
        match self {
            Self::Sound => "unsound",
            Self::Complete => "incomplete",
        }
    }
}

fn op_pat_string(o: &OpPattern) -> String {
    match o {
        OpPattern::Const => format!("const"),
        OpPattern::Eq => format!("="),
        OpPattern::Ite => format!("ite"),
        OpPattern::Not => format!("not"),
        OpPattern::Implies => format!("=>"),
        OpPattern::BoolMaj => format!("maj"),
        OpPattern::BoolNaryOp(o) => format!("{}", o),
        OpPattern::PfNaryOp(o) => format!("{}", o),
        OpPattern::PfUnOp(o) => format!("{}", o),
        OpPattern::BvBit => format!("bit"),
        OpPattern::BvBinOp(o) => format!("{}", o),
        OpPattern::BvBinPred(o) => format!("{}", o),
        OpPattern::BvNaryOp(o) => format!("{}", o),
        OpPattern::BvUnOp(o) => format!("{}", o),
        OpPattern::BoolToBv => format!("bool2bv"),
        OpPattern::BvExtract => format!("bvextract"),
        OpPattern::BvConcat => format!("bvconcat"),
        OpPattern::BvUext => format!("bvuext"),
        OpPattern::BvSext => format!("bvsext"),
        OpPattern::PfToBv => format!("pf2bv"),
        OpPattern::UbvToPf => format!("ubv2pf"),
    }
}

fn sort_pat_string(s: &SortPat) -> String {
    match s {
        SortPat::Bool => format!("bool"),
        SortPat::BitVector => format!("bitvector"),
        SortPat::Field => format!("field"),
    }
}

fn main() -> Result<(), String> {
    env_logger::Builder::from_default_env()
        .format_level(false)
        .format_timestamp(None)
        .init();
    let opts = dbg!(Options::from_args());
    let props = if opts.properties.is_empty() {
        vec![Prop::Sound, Prop::Complete]
    } else {
        opts.properties.clone()
    };
    let rule_types = if opts.rule_types.is_empty() {
        vec![RuleType::Enc, RuleType::Var, RuleType::Conv]
    } else {
        opts.rule_types.clone()
    };
    let bnd = Bound {
        args: opts.max_args,
        bv_bits: opts.max_bv_bits,
        field: DFL_T.clone(),
    };

    if rule_types.contains(&RuleType::Conv) {
        if props.contains(&Prop::Sound) {
            for (from, to, s, t) in c_soundness_terms::<Enc>(&bnd) {
                println!("check: sound conversion {:?} -> {:?} : {}", from, to, s);
                if let Some(model) = find_model(&t) {
                    println!("ERROR: unsound");
                    println!(
                        "Formula:\n{}\n",
                        pp_sexpr(serialize_term(&t).as_bytes(), 100)
                    );
                    println!(
                        "Counterexample: {}",
                        serialize_value_map(&model.into_iter().collect())
                    );
                    return Err(format!("ERROR"));
                }
            }
        }
        if props.contains(&Prop::Complete) {
            for (from, to, s, t) in c_completeness_terms::<Enc>(&bnd) {
                println!("check: complete conversion {:?} -> {:?} : {}", from, to, s);
                if let Some(model) = find_model(&t) {
                    println!("ERROR: unsound");
                    println!(
                        "Formula:\n{}\n",
                        pp_sexpr(serialize_term(&t).as_bytes(), 100)
                    );
                    println!(
                        "Counterexample: {}",
                        serialize_value_map(&model.into_iter().collect())
                    );
                    return Err(format!("ERROR"));
                }
            }
        }
    }

    if rule_types.contains(&RuleType::Var) {
        if props.contains(&Prop::Complete) {
            for (s, t) in v_completeness_terms::<Enc>(&bnd) {
                println!("check: variable {}", s);
                if let Some(model) = find_model(&t) {
                    println!("ERROR");
                    println!(
                        "Formula:\n{}\n",
                        pp_sexpr(serialize_term(&t).as_bytes(), 100)
                    );
                    println!(
                        "Counterexample: {}",
                        serialize_value_map(&model.into_iter().collect())
                    );
                    return Err(format!("ERROR"));
                }
            }
        }
        if props.contains(&Prop::Sound) {
            for (s, t) in v_soundness_terms::<Enc>(&bnd) {
                println!("check: variable {}", s);
                if let Some(model) = find_model(&t) {
                    println!("ERROR");
                    println!(
                        "Formula:\n{}\n",
                        pp_sexpr(serialize_term(&t).as_bytes(), 100)
                    );
                    println!(
                        "Counterexample: {}",
                        serialize_value_map(&model.into_iter().collect())
                    );
                    return Err(format!("ERROR"));
                }
            }
        }
    }

    if rule_types.contains(&RuleType::Enc) {
        for r in rules() {
            let op_ok = opts.ops.is_empty() || opts.ops.contains(&op_pat_string(&r.pattern().0));
            let ex_op_ok = !opts.excluded_ops.contains(&sort_pat_string(&r.pattern().1));
            let sort_ok =
                opts.sorts.is_empty() || opts.sorts.contains(&sort_pat_string(&r.pattern().1));
            if op_ok && ex_op_ok && sort_ok {
                for prop in &props {
                    let f = match prop {
                        Prop::Sound => soundness_terms,
                        Prop::Complete => completeness_terms,
                    };
                    for (t, s, soundness) in f(&r, &bnd) {
                        println!("check: {:?} {} {}", prop, t, s);
                        if let Some(model) = find_model(&soundness) {
                            println!("ERROR: {}", prop.failure_message());
                            println!(
                                "Formula:\n{}\n",
                                pp_sexpr(serialize_term(&soundness).as_bytes(), 100)
                            );
                            println!(
                                "Counterexample: {}",
                                serialize_value_map(&model.into_iter().collect())
                            );
                            return Err(format!("ERROR: {}", prop.failure_message()));
                        }
                    }
                }
            }
        }
    }
    Ok(())
}
