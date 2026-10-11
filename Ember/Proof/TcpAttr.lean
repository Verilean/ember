import Lean

/-!
# Ember.Proof.TcpAttr — the simp set that executes TCP code symbolically

`tcpsym` collects the lemmas with which `simp only [tcpsym, …]` steps
through a function of `Ember/Net/Tcp.lean` on a state `tcpSt st w`
(`RefineTcpSt.lean`): statements, expressions, the fields of `t` and
`sg`, the constants.  (An attribute has to be declared in a module of its
own before it is used.)
-/

/-- Lemmas that execute the TCP code symbolically. -/
register_simp_attr tcpsym
