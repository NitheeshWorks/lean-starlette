import LeanStarlette.RepoImpl.Responses

/-!
# RepoImpl: `HTTPException` and its default handler

`starlette/exceptions.py` and `ExceptionMiddleware.http_exception`. The
reason phrases are Python's `http.client.responses`.
-/

namespace LeanStarlette

/-- `http.client.responses[status]`, or `""`. -/
def reasonPhrase : Nat → String
  | 100 => "Continue" | 101 => "Switching Protocols" | 102 => "Processing" | 103 => "Early Hints"
  | 200 => "OK" | 201 => "Created" | 202 => "Accepted" | 203 => "Non-Authoritative Information"
  | 204 => "No Content" | 205 => "Reset Content" | 206 => "Partial Content" | 207 => "Multi-Status"
  | 208 => "Already Reported" | 226 => "IM Used"
  | 300 => "Multiple Choices" | 301 => "Moved Permanently" | 302 => "Found" | 303 => "See Other"
  | 304 => "Not Modified" | 305 => "Use Proxy" | 307 => "Temporary Redirect" | 308 => "Permanent Redirect"
  | 400 => "Bad Request" | 401 => "Unauthorized" | 402 => "Payment Required" | 403 => "Forbidden"
  | 404 => "Not Found" | 405 => "Method Not Allowed" | 406 => "Not Acceptable"
  | 407 => "Proxy Authentication Required" | 408 => "Request Timeout" | 409 => "Conflict"
  | 410 => "Gone" | 411 => "Length Required" | 412 => "Precondition Failed"
  | 413 => "Content Too Large" | 414 => "URI Too Long" | 415 => "Unsupported Media Type"
  | 416 => "Range Not Satisfiable" | 417 => "Expectation Failed" | 418 => "I'm a Teapot"
  | 421 => "Misdirected Request" | 422 => "Unprocessable Content" | 423 => "Locked"
  | 424 => "Failed Dependency" | 425 => "Too Early" | 426 => "Upgrade Required"
  | 428 => "Precondition Required" | 429 => "Too Many Requests"
  | 431 => "Request Header Fields Too Large" | 451 => "Unavailable For Legal Reasons"
  | 500 => "Internal Server Error" | 501 => "Not Implemented" | 502 => "Bad Gateway"
  | 503 => "Service Unavailable" | 504 => "Gateway Timeout" | 505 => "HTTP Version Not Supported"
  | 506 => "Variant Also Negotiates" | 507 => "Insufficient Storage" | 508 => "Loop Detected"
  | 510 => "Not Extended" | 511 => "Network Authentication Required"
  | _ => ""

/-- `HTTPException(status_code, detail=None, headers=None)`: `detail`
defaults to the reason phrase. -/
def HTTPException (status_code : Nat) (detail : Option String := none)
    (headers : List (String × String) := []) (h : StatusCode.Valid status_code := by decide) : Exception :=
  .http status_code (detail.getD (reasonPhrase status_code)) headers h

namespace Exception

/-- `str(exc)`: `"404: Not Found"`. -/
def toStr : Exception → String
  | .http s d _ _ => s!"{s}: {d}"
  | .custom k d _ => s!"{k}: {d}"

instance : ToString Exception := ⟨toStr⟩

/-- `exc.status_code` of an `HTTPException`. -/
def statusCode? : Exception → Option Nat
  | .http s _ _ _ => some s
  | .custom .. => none

end Exception

/-- `ExceptionMiddleware.http_exception`: the default response for an
`HTTPException`. A 204 or 304 gets no body. -/
def httpExceptionResponse (status_code : Nat) (detail : String) (headers : List (String × String))
    (h : StatusCode.Valid status_code) : Response :=
  if status_code == 204 || status_code == 304 then Response.make {} status_code headers none h
  else Response.make detail status_code headers (some "text/plain") h

end LeanStarlette
