import LeanStarlette.RepoImpl.Template

/-!
# Specifications: lawful convertors and separated templates

The two hypotheses of the routing round trip.

* `Convertor.Lawful c`: the convertor's `render` (upstream `to_string`)
  produces strings its recogniser accepts and `convert` inverts, and accepted
  strings only use `allowed` characters.
* `Template.Separated t`: every parameter is either last or followed by a
  literal whose first character the parameter cannot contain, so a greedy
  match cannot run past it. `/users/{id}/edit`, `/int/{n:int}` and
  `/path-with-parentheses({param:int})` are separated; `/{a}{b}` is not, and
  its round trip is genuinely false (`a=x, b=yz` renders `/xyz`, which matches
  `a=xy, b=z`).
-/

namespace LeanStarlette

/-- The convertor laws. -/
structure Convertor.Lawful (c : Convertor) : Prop where
  allowed_of_accepts : ∀ s, c.accepts s = true → ∀ ch ∈ s, c.allowed ch = true
  accepts_render : ∀ v s, c.render v = some s → c.accepts s = true
  convert_render : ∀ v s, c.render v = some s → c.convert s = v
  render_convert : ∀ s, c.accepts s = true → (c.render (c.convert s)).isSome = true

/-- No parameter can swallow the piece after it. -/
def separatedPieces : List Piece → Bool
  | [] => true
  | .lit _ :: ps => separatedPieces ps
  | .param _ c :: ps =>
    (match ps with
      | [] => true
      | .lit (ch :: _) :: _ => !c.allowed ch
      | _ => false) && separatedPieces ps

/-- A template whose parameters are delimited. Decidable. -/
def Template.Separated (t : Template) : Prop := separatedPieces t.pieces = true

instance (t : Template) : Decidable t.Separated := inferInstanceAs (Decidable (_ = _))

/-- Every convertor in the template is lawful. -/
def Template.Lawful (t : Template) : Prop :=
  ∀ n c, Piece.param n c ∈ t.pieces → c.Lawful

/-- Equal as dictionaries: Python compares `path_params` dicts this way. -/
def PathParams.Equiv (a b : PathParams) : Prop := ∀ k, a.lookup k = b.lookup k

end LeanStarlette
