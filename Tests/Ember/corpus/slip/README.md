# slip/ — RFC 1055 framing

Hand-written scenarios (`slip` list in `Tests/Ember/Scenarios.lean`):
escapes in the payload, empty frames, a frame split across chunks, two
frames in one chunk, an oversize frame, `ESC` before an ordinary byte,
line noise.  The decoder's choices follow the Linux SLIP driver (see
`Ember/Spec/Slip.lean`).
