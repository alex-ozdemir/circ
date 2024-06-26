//! Operator PersistentRamSplit

use crate::ir::term::ty::*;
use crate::ir::term::*;
use fxhash::FxHashSet as HashSet;

/// Type-check [super::ExtOp::PersistentRamSplit].
pub fn check(arg_sorts: &[&Sort]) -> Result<Sort, TypeErrorReason> {
    let &[entries, indices] = ty::count_or_ref(arg_sorts)?;
    let (size, value) = ty::homogenous_tuple_or(entries, "PersistentRamSplit entries")?;
    let [old, new] = ty::count_or(ty::tuple_or(value, "PersistentRamSplit entries")?)?;
    eq_or(old, new, "PersistentRamSplit entries")?;
    let (i_size, i_value) = ty::homogenous_tuple_or(indices, "PersistentRamSplit indices")?;
    let f = pf_or(i_value, "PersistentRamSplit indices")?;
    let n_touched = i_size.min(size);
    let n_ignored = size - n_touched;
    let f_pair = Sort::new_tuple(vec![f.clone(), f.clone()]);
    let ignored_entries_sort = Sort::Tuple(vec![f_pair.clone(); n_ignored].into());
    let selected_entries_sort = Sort::Tuple(vec![f_pair.clone(); n_touched].into());
    Ok(Sort::new_tuple(vec![
        ignored_entries_sort,
        selected_entries_sort.clone(),
        selected_entries_sort,
    ]))
}

/// Evaluate [super::ExtOp::PersistentRamSplit].
///
/// Takes two arguments:
///
/// * entries: `[(val_init_i, val_fin_i)]` (len E)
/// * indices: `[idx_i]` (len I)
///
/// assumes I < E and 0 <= idx_i < E.
///
/// Let dedup_i be idx_i with duplicates removed
/// Let ext_i be dedup_i padded up to length I. The added elements are each i in 0.. (so long as i hasn't occured in ext_i already).
/// Let
///
///
/// Returns:
/// * a bunch of sequences of index-value pairs:
///   * untouched_entries (array field (tuple (field field)) (length I - E))
///   * init_reads (array field (tuple (field field)) (length I))
///   * fin_writes (array field (tuple (field field)) (length I))
pub fn eval(args: &[&Value]) -> Value {
    let entries = &args[0].as_tuple();
    let (init_vals, fin_vals): (Vec<Value>, Vec<Value>) = entries
        .iter()
        .map(|t| (t.as_tuple()[0].clone(), t.as_tuple()[1].clone()))
        .unzip();
    let indices = &args[1].as_tuple();
    let num_accesses = indices.len();
    let field = args[1].sort().as_tuple()[0].as_pf().clone();
    let uniq_indices = {
        let mut uniq_indices = Vec::<usize>::new();
        let mut used_indices = HashSet::<usize>::default();
        for i in indices.iter().map(|i| i.as_usize().unwrap()).chain(0..) {
            if uniq_indices.len() == num_accesses {
                break;
            }
            if !used_indices.contains(&i) {
                uniq_indices.push(i);
                used_indices.insert(i);
            }
        }
        uniq_indices.sort();
        uniq_indices
    };
    let mut init_reads = Vec::new();
    let mut fin_writes = Vec::new();
    let mut untouched_entries = Vec::new();
    let mut j = 0;
    for (i, (init_val, fin_val)) in init_vals.into_iter().zip(fin_vals).enumerate() {
        if j < uniq_indices.len() && uniq_indices[j] == i {
            init_reads.push((i, init_val));
            fin_writes.push((i, fin_val));
            j += 1;
        } else {
            untouched_entries.push((i, init_val));
        }
    }
    let entry_to_vals =
        |e: (usize, Value)| Value::Tuple(Box::new([Value::Field(field.new_v(e.0)), e.1]));
    let vec_to_tuple = |v: Vec<(usize, Value)>| {
        let vals: Vec<Value> = v.into_iter().map(entry_to_vals).collect();
        Value::Tuple(vals.into())
    };
    let init_reads = vec_to_tuple(init_reads);
    let untouched_entries = vec_to_tuple(untouched_entries);
    let fin_writes = vec_to_tuple(fin_writes);
    Value::Tuple(vec![untouched_entries, init_reads, fin_writes].into_boxed_slice())
}
