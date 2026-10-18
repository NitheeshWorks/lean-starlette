import LeanStarlette
import Plausible

/-!
# Plausible properties

Randomised checks run at build time with `plausible` (`#eval
Testable.check`, which fails the build on a counter-example): the
percent-encoding and query-string round trips that are tested rather than
proved, and case-insensitive header lookup on plausible's own generators.
-/

namespace Pbt

open LeanStarlette

#eval Plausible.Testable.check (∀ s : String, unquote (quote s []) = s)

#eval Plausible.Testable.check (∀ s : String, unquotePlus (quotePlus s) = s)

#eval Plausible.Testable.check (∀ s : String, String.ofList (decodeUtf8 s.toUTF8.toList) = s)

#eval Plausible.Testable.check (∀ (k v : String),
    (QueryParams.parse (toString (QueryParams.mk [(k, v)]))).items = [(k, v)])

#eval Plausible.Testable.check (∀ (k v : String),
    (Headers.ofList [(k, v)]).get? (upperAscii k) = some v)

end Pbt
