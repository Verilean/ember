import Ember.Util.Bytes
import Ember.Util.Str
import Ember.Util.Rand
import Ember.Util.Pretty
import Ember.Util.Pcap
import Ember.Trace.Event
import Ember.Trace.Text
import Ember.Trace.Diff
import Ember.Spec.Stack
import Ember.Spec.Peer
import Ember.Spec.Scenario
import Ember.Spec.Gen
import Ember.Lang.Syntax
import Ember.Lang.Types
import Ember.Lang.Eval
import Ember.Lang.Surface
import Ember.Lang.Profile
import Ember.Lang.Pretty
import Ember.Lang.Gen
import Ember.Lang.Examples
import Ember.C.Ast
import Ember.C.Print
import Ember.C.Compile
import Ember.Net.Main
import Ember.Tools.Cli
import Ember.Tools.Host
import Ember.Tools.Cc
import Ember.Tools.Emit
import Ember.Tools.Fuzz
import Ember.Tools.GenRun
import Ember.Tools.NetCheck
import Ember.Tools.Lockstep

/-!
# Ember

A TCP/IP stack in Lean (`Ember.Spec`), a Lean-hosted DSL that emits
UB-free C (`Ember.Lang`, `Ember.C`), and the stack written in that DSL
(`Ember.Net`), cross-checked through one trace format (`Ember.Trace`).
See `docs/Ember-design.md` and `docs/Ember-plan.md`.
-/
