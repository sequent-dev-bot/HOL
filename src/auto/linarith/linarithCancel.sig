signature linarithCancel =
sig
  include Abbrev

  (* Syntax and AC theorems of one carrier's addition, as consumed by
     the cancellation step of mk_norm_conv.  ac_fallback is an optional
     additive normalizer used when AC_CONV alone cannot justify a
     rearrangement. *)
  type ac_ops = {
    dest_less : term -> term * term,
    dest_leq : term -> term * term,
    strip_plus : term -> term list,
    mk_plus : term * term -> term,
    assoc : thm,
    comm : thm,
    rid : thm,
    ac_fallback : conv option
  }

  (* The data an instance's norm_conv is made of: the carrier's three
     left-cancellation theorems, the polynomial normalizer for its
     expressions, the literal reducer, and the reflexivity theorems that
     decide a relation between equal sides.  expression_conv is expected
     to decline a term outside the carrier by raising UNCHANGED; build
     it with mk_expression_conv, which is that contract. *)
  type norm_spec = {
    ac : ac_ops,
    ty : hol_type,
    leq_cancel : thm,
    less_cancel : thm,
    eq_cancel : thm,
    expression_conv : conv,
    reduce_conv : conv,
    refl_thms : thm list
  }

  (* safe_conv conv is conv made total: neither a HOL_ERR failure nor an
     UNCHANGED decline escapes it, so a step with nothing to say
     contributes a reflexivity theorem rather than stopping the chain it
     sits in. *)
  val safe_conv : conv -> conv

  (* mk_expression_conv ty convs is the expression_conv of a carrier
     whose expressions are normalized by convs, applied left to right:
     it runs them on a term of type ty and declines a term of any other
     type by raising UNCHANGED, which is the norm_spec contract above.
     Carriers differ in how far a step may fail — an instance wraps the
     steps that only sometimes apply in safe_conv or TRY_CONV itself —
     so the guard is what mk_expression_conv exists to share. *)
  val mk_expression_conv : hol_type -> conv list -> conv

  (* The whole of an instance's norm_conv: cancel down a relation of this
     carrier, and normalize anything else as an expression.  Which of the
     two a term is has to be decided before the conversions run, because
     ORELSEC catches HOL_ERR only, so an alternative that signals "not
     mine" by raising UNCHANGED is never reached past. *)
  val mk_norm_conv : norm_spec -> conv
end
