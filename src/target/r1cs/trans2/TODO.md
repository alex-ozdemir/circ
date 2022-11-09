To do:
* bv: shl
* bv: ashr
* bv: lshr
* ff: recip (incomplete)
* ff: const (timeout)
* ff: ubv2pf (timeout)
* secret/public variables
* field flatten
* better Pf2Bv in SMT BE

Done:
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
* bv: pf2bv
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
