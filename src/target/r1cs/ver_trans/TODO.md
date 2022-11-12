To do:
* ff: const (timeout)
* bv: pf2bv (incomplete)
* secret/public variables
* field flatten
* better Pf2Bv in SMT BE

Done:
* ff: ubv2pf
* bv: shl
* bv: ashr
* bv: lshr
* bv: urem
* bv: udiv
* bv: predicates
* bv: sub
* bv: concat
* bv: extract
* bv: mul
* bv: add
* ff: ite
* ff: add
* ff: mul
* ff: neg
* ff: recip (incomplete)
* bv: and
* bv: or
* bv: xor
* clean visibilities
* heterogeneous input encodings (BV ITE)
* fix variable soundness VC (universal quantifiers)
* FE filters for rule types
* conversion completeness VC
* variable completeness VC
* conversion soundness VC
* Improve FE output for param'd sort patterns
* re-org traits
* basic Pf2Bv in SMT BE
* verification FE filtering on ops, sorts
* completeness
* boolean ITE
* encoding polymorphism (attempt 1):
  * encodings and encoding types
  * rule types: rules, variable rules, conversion rules
  * encoding type chooser
* input encoding for booleans
* boolean majority
* fix boolean constant VC

Bugs found:
* ff recip
  * incomplete on input 0
  * fix with:
    * xi = 1 - z
    * xz = 0
    * iz = 0
  * undesirable: adds *two* constraints...
  * could achieve non-det, complete semantics with only one extra constraint:
    * xxi = x
    * but it's unclear how to define soundness
* bv shifts
  * only applied to widths that are powers of 2
  * incomplete on oversized shift amounts (asserted value in range)
  * the obvious way to recover completeness (remove assertion) was unsound
    * it mod'd the shift amount rather than saturating it.
  * now: SMT-LIB compliant
* bv cmp
  * based on an unsound (in the original implementation) XOR incomplete (in
    our port) 'fits in bits' check.
  * fixed now.
* bv{udiv,urem}
  * differed from SMT standard
