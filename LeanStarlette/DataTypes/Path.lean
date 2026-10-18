import LeanJson
import LeanStarlette.DataTypes.Chars

/-!
# DataTypes: path parameters, convertors and path templates

Starlette compiles a route path such as `/users/{username}` or
`/int/{param:int}` into a regular expression with one named group per
parameter (`starlette/routing.py`, `compile_path`). Here a template is a list
of pieces instead: literal text, and parameters carrying a `Convertor`, a
total recogniser standing in for the convertor's regular expression.

This is the routing theory the stack plan puts in `Keel.Route`; until that
module publishes its API it lives here in the same shape (a general
`Convertor` law, then five instances), so the move is mechanical.
-/

namespace LeanStarlette

/-- A UUID in canonical form: 32 lower-case hexadecimal digits. Python's
`uuid.UUID` normalises to this, and `str(uuid)` prints it with hyphens. -/
structure UUID where
  hex : List Char
  h_len : hex.length = 32
  h_hex : ∀ c ∈ hex, isLowerHex c = true

instance : DecidableEq UUID := fun a b =>
  if h : a.hex = b.hex then isTrue (by cases a; cases b; simp_all)
  else isFalse (by intro e; cases e; exact h rfl)

/-- A converted path parameter: what `request.path_params[...]` holds in
Starlette (`str`, `int`, `float` or `uuid.UUID`). Floats are exact
non-negative decimals, not IEEE doubles (see `CONTRIBUTING.md`). -/
inductive PathValue where
  | str (s : String)
  | int (n : Nat)
  | float (d : LeanJson.Decimal)
  | uuid (u : UUID)
  deriving DecidableEq

/-- A path convertor (`starlette/convertors.py`): a recogniser for the
characters a parameter may match, the conversion to a value, and the inverse
used by `url_path_for`. `render` returns `none` where upstream's `to_string`
fails an assertion (an empty or `/`-containing string, a negative number).

* `accepts s`: `s` is in the language of the convertor's regular expression.
* `allowed c`: `c` can occur in some accepted string; routing uses it to see
  where a parameter must stop.

The laws a convertor must satisfy are `Convertor.Lawful`
(`Specifications/Routing.lean`); the five built-in ones are proved lawful. -/
structure Convertor where
  /-- The key in `CONVERTOR_TYPES`: `str`, `path`, `int`, `float`, `uuid`. -/
  name : String
  /-- Upstream's regular expression, for documentation. -/
  regex : String
  accepts : List Char → Bool
  allowed : Char → Bool
  convert : List Char → PathValue
  render : PathValue → Option (List Char)

/-- One piece of a compiled path template. -/
inductive Piece where
  | lit (text : List Char)
  | param (name : String) (conv : Convertor)

/-- The parameter name of a piece, if it is one. -/
def Piece.paramName? : Piece → Option String
  | .lit _ => none
  | .param n _ => some n

/-- A compiled path template. Parameter names are distinct (upstream raises
`ValueError("Duplicated param name ...")` otherwise), and that is a field. -/
structure Template where
  /-- The path as written, e.g. `/users/{username}`. -/
  source : String
  pieces : List Piece
  h_nodup : (pieces.filterMap Piece.paramName?).Nodup

/-- The parameter names of a template, in order. -/
def Template.paramNames (t : Template) : List String :=
  t.pieces.filterMap Piece.paramName?

/-- Converted path parameters, in template order: Starlette's
`request.path_params` dict. -/
abbrev PathParams := List (String × PathValue)

end LeanStarlette
