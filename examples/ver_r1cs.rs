use circ::ir::term::text::*;
use circ::target::r1cs::ver_trans::{
    rules::Enc,
    ver::{Bound, VerifiableEncoding},
};
use circ::target::smt::find_model;
use circ::util::field::DFL_T;
use fxhash::FxHashMap;
use std::collections::{BTreeMap, BTreeSet};
use std::str::FromStr;
use structopt::StructOpt;

use std::time::Instant;

#[derive(Debug, StructOpt)]
#[structopt(name = "ver_r1cs", about = "Verifier for CirC's R1CS lowering pass")]
struct Options {
    #[structopt(long, short = "a", default_value = "2")]
    /// The maximum number of arguments
    max_args: usize,

    #[structopt(long, short = "b", default_value = "2")]
    /// The maximum width of any bit-vector
    max_bv_bits: usize,

    #[structopt(long, short = "l")]
    /// Don't verify anything, just list tags for the VCs
    list_tags: bool,

    #[structopt(long, short, default_value = "")]
    include: Filter,

    #[structopt(long, short)]
    exclude: Vec<Filter>,
}

#[derive(Debug)]
struct Test {
    key: String,
    op: Op,
    value: String,
}

impl Test {
    fn new(k: &str, op: Op, v: &str) -> Self {
        Test {
            key: k.to_lowercase(),
            op,
            value: v.to_lowercase(),
        }
    }
    fn matches(&self, tags: &FxHashMap<String, String>) -> bool {
        if let Some(v) = tags.get(&self.key) {
            match self.op {
                Op::Gt => usize::from_str(v).unwrap() > usize::from_str(&self.value).unwrap(),
                Op::Ge => usize::from_str(v).unwrap() >= usize::from_str(&self.value).unwrap(),
                Op::Lt => usize::from_str(v).unwrap() < usize::from_str(&self.value).unwrap(),
                Op::Le => usize::from_str(v).unwrap() <= usize::from_str(&self.value).unwrap(),
                Op::Eq => v == &self.value,
                Op::Ne => v != &self.value,
            }
        } else {
            false
        }
    }
}

#[derive(Debug)]
enum Op {
    Gt,
    Ge,
    Lt,
    Le,
    Eq,
    Ne,
}

#[derive(Debug)]
struct Filter(Vec<Test>);

impl Filter {
    fn matches(&self, tags: &FxHashMap<String, String>) -> bool {
        self.0.iter().all(|f| f.matches(tags))
    }
}

impl FromStr for Test {
    type Err = String;

    fn from_str(s: &str) -> Result<Self, Self::Err> {
        if let Some(i) = s.find("!=") {
            Ok(Self::new(&s[..i], Op::Ne, &s[i + 2..]))
        } else if let Some(i) = s.find(">=") {
            Ok(Self::new(&s[..i], Op::Ge, &s[i + 2..]))
        } else if let Some(i) = s.find("<=") {
            Ok(Self::new(&s[..i], Op::Le, &s[i + 2..]))
        } else if let Some(i) = s.find("=") {
            Ok(Self::new(&s[..i], Op::Eq, &s[i + 1..]))
        } else if let Some(i) = s.find(">") {
            Ok(Self::new(&s[..i], Op::Gt, &s[i + 1..]))
        } else if let Some(i) = s.find("<") {
            Ok(Self::new(&s[..i], Op::Lt, &s[i + 1..]))
        } else {
            Err(format!(
                "Could not find operator in {}; ops: {{=, !=, >=, <=, >, <}}",
                s
            ))
        }
    }
}

impl FromStr for Filter {
    type Err = String;

    fn from_str(s: &str) -> Result<Self, Self::Err> {
        let mut o = Vec::new();
        for seg in s.trim().split(",") {
            if !seg.is_empty() {
                o.push(Test::from_str(seg.trim())?);
            }
        }
        Ok(Filter(o))
    }
}

fn main() -> Result<(), String> {
    env_logger::Builder::from_default_env()
        .format_level(false)
        .format_timestamp(None)
        .init();
    let opts = dbg!(Options::from_args());
    let bnd = Bound {
        args: opts.max_args,
        bv_bits: opts.max_bv_bits,
        field: DFL_T.clone(),
    };

    let all_vcs = <Enc as VerifiableEncoding>::all_vcs(&bnd);

    if opts.list_tags {
        let mut tags_and_values: BTreeMap<String, BTreeSet<String>> = Default::default();
        for vc in all_vcs {
            for (k, v) in vc.tags {
                tags_and_values.entry(k).or_default().insert(v);
            }
        }
        println!("Tags and values:");
        for (k, vs) in tags_and_values {
            print!(" {} =", k);
            for v in vs {
                print!(" {},", v);
            }
            println!("");
        }
    } else {
        for vc in all_vcs {
            let included = opts.include.matches(&vc.tags);
            let excluded = opts.exclude.iter().any(|f| f.matches(&vc.tags));
            if included && !excluded {
                println!("VC tags:");
                for (k, v) in &vc.tags {
                    println!(" {} = {}", k, v);
                }
                let start = Instant::now();
                if let Some(model) = find_model(&vc.formula) {
                    println!("ERROR:");
                    println!(
                        "Formula:\n{}\n",
                        pp_sexpr(serialize_term(&vc.formula).as_bytes(), 100)
                    );
                    println!(
                        "Counterexample: {}",
                        serialize_value_map(&model.into_iter().collect())
                    );
                    return Err(format!("ERROR"));
                }
                println!("Verified in {}s", start.elapsed().as_secs_f64());
            }
        }
    }
    Ok(())
}
