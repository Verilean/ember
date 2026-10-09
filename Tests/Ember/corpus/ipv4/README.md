# ipv4/ — header validation

Hand-written scenarios (`ipv4` list in `Tests/Ember/Scenarios.lean`):
one fixture per check in `Ember.Spec.Ipv4.validate`, each a ping with one
field mutated (checksum fixed unless the checksum is the point), and the
expected `drop reason=`.  `options` and `padding` are accepted inputs.
