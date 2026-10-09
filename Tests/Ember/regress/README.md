# regress/ — shrunk failures

`lake exe ember-gen` (and later `ember-fuzz`, `ember-lockstep`) write the
minimal input stream of every failure here as a trace fixture; `lake
test` replays this directory with the corpus.  A file stays after its
bug is fixed, as a regression test.

Divergences between the interpreter and the emitted C found by
`ember-fuzz` are kept as Ember programs instead, in
`Tests/Ember/LangPrograms.lean` (`Regress`), where the differential suite
runs them.
