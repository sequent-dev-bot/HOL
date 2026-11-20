(* The unfolding's questions about a constant as they were answered before
   they were answered from tables built once: by walking the context's lists
   and the type base for every occurrence, and by looking the definition up in
   the theory's tables every time.  Kept as the reference the selftest
   compares the tables with, each walk counted as the context's registry
   enumerations.  Copied from the model finder's source before the change; do
   not "improve" it. *)
structure refuteLookupReference =
struct
  structure MFH = Refute_ModelFinder_HOL

  fun scanning (context : MFH.mf_context) : MFH.lookups =
    let
      val {case_names, whacks, ersatz_table, def_tables, counts, ...} = context
      fun scan () = MFH.tick (#registry_scans counts)

      fun case_info constant =
        let val key = MFH.const_key constant
        in
          scan ();
          Option.map #2 (List.find (fn (other, _) =>
            KernelSig.name_compare (key, other) = EQUAL) case_names)
        end

      fun whack_matches pattern candidate =
        case (Lib.total Term.dest_thy_const pattern,
              Lib.total Term.dest_thy_const candidate) of
            (SOME {Thy = pattern_thy, Name = pattern_name, ...},
             SOME {Thy = actual_thy, Name = actual_name, ...}) =>
              pattern_thy = actual_thy andalso
              pattern_name = actual_name andalso
              MFH.type_matches_unboxed
                (Term.type_of pattern, Term.type_of candidate)
          | _ => Term.aconv pattern candidate
      fun whacked candidate =
        (scan ();
         List.exists (fn pattern => whack_matches pattern candidate) whacks)

      fun replacement constant =
        let val key = MFH.const_key constant
        in
          scan ();
          case List.find (fn ({original, ...} : MFH.ersatz) =>
                 KernelSig.name_compare (original, key) = EQUAL)
                 ersatz_table of
              SOME {replacement = {Thy, Name}, ...} =>
                SOME (MFH.retype_constant "ersatz"
                  (Term.prim_mk_const {Thy = Thy, Name = Name})
                  (Term.type_of constant))
            | NONE => NONE
        end

      fun ersatz_call original candidate =
        if not (Term.is_const candidate) then false
        else
          let
            val original_key = MFH.const_key original
            val candidate_key = MFH.const_key candidate
          in
            scan ();
            List.exists (fn ({original = source, replacement} : MFH.ersatz) =>
              KernelSig.name_compare (source, original_key) = EQUAL andalso
              KernelSig.name_compare (replacement, candidate_key) = EQUAL andalso
              Term.type_of original = Term.type_of candidate) ersatz_table
          end handle Feedback.HOL_ERR _ => false

      fun find_field which term =
        let
          val key = MFH.original_const_key term
          fun search_type info =
            let
              fun search (_, []) = NONE
                | search (index, (_, data) :: rest) =
                    if KernelSig.name_compare
                         (MFH.original_const_key (which data), key) = EQUAL
                    then SOME index
                    else search (index + 1, rest)
            in
              search (0, TypeBasePure.fields_of info)
            end
        in
          scan ();
          Lib.get_first search_type (Refute_TypeBase.elts ())
        end handle Feedback.HOL_ERR _ => NONE

      fun definition constant =
        (MFH.tick (#definitions counts);
         Option.map (fn (force, definition) =>
           (force, definition, Term.term_size definition))
           (MFH.raw_def_of_const_ext def_tables constant))
    in
      {case_info = case_info, whacked = whacked, replacement = replacement,
       ersatz_call = ersatz_call,
       record_get = find_field #accessor, record_update = find_field #fupd,
       definition = definition}
    end
end
