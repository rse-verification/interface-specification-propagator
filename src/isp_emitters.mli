(** This module contains the behaviour the is currently being generated for the currently visited function. *)
module type Behavior = sig
  val reset_current_behavior : unit -> unit
  (** Rests the current behaviour to an empty behaviour. *)

  val get_current_behavior : unit -> Cil_types.behavior
  (** Gets the behaviour for the currently visited function. *)
end

module Behavior : Behavior

(** The emitters related to auxiliary specifications.
    Todo: This needs to be refactored. Auxiliary specifications are not part
    of Interface specifications. It's the other way around *)
module type Auxiliary = sig
  val emit :
    Cil_types.exp option ->
    Eva.Results.request(*Db.Value.state*) ->       (*Change pending*)
    Cil_types.kernel_function ->
    (unit -> unit) Queue.t ->
    unit
  (** Emit the the behavior contract of the given function. 
      Todo: Consider renameing this function.*)
end

module Auxiliary : Auxiliary
