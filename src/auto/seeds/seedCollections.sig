signature seedCollections =
sig
  include Abbrev

  val algebra_rewrites : unit -> thm list
  val field_rewrites : unit -> thm list

  val algebra_ss : unit -> simpLib.ssfrag
  val field_ss : unit -> simpLib.ssfrag

  val remove_algebra_simps : string -> unit
  val remove_field_simps : string -> unit
end
