/-! String helpers that paper over the `String.Slice` API of recent Lean. -/

namespace Ember.Str

def trim (s : String) : String := s.trimAscii.toString
def trimL (s : String) : String := s.trimAsciiStart.toString
def trimR (s : String) : String := s.trimAsciiEnd.toString

/-- Whitespace-separated words. -/
def words (s : String) : List String :=
  ((s.split (fun c : Char => c.isWhitespace)).toList.map (·.toString)).filter (· ≠ "")

def padRight (s : String) (n : Nat) : String :=
  s ++ String.ofList (List.replicate (n - s.length) ' ')

def padLeft (s : String) (n : Nat) (c : Char := ' ') : String :=
  String.ofList (List.replicate (n - s.length) c) ++ s

end Ember.Str
