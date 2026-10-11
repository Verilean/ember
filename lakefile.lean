import Lake
open Lake DSL

package «ember» where

-- Same pin as Sparkle (verified against v4.32.1).
require LSpec from git
  "https://github.com/argumentcomputer/LSpec" @ "3e23a4a"

@[default_target]
lean_lib «Ember» where

lean_lib «Tests» where

@[test_driver]
lean_exe «test» where
  root := `Tests.AllTests

lean_exe «ember-diff» where
  root := `Tests.Ember.Drivers.DiffMain

lean_exe «ember-pcap» where
  root := `Tests.Ember.Drivers.PcapMain

lean_exe «ember-host» where
  root := `Tests.Ember.Drivers.HostMain

lean_exe «ember-emit» where
  root := `Tests.Ember.Drivers.EmitMain

lean_exe «ember-fuzz» where
  root := `Tests.Ember.Drivers.FuzzMain

lean_exe «ember-lockstep» where
  root := `Tests.Ember.Drivers.LockstepMain

lean_exe «ember-replay» where
  root := `Tests.Ember.Drivers.ReplayMain

lean_exe «ember-fixtures» where
  root := `Tests.Ember.Drivers.FixturesMain

lean_exe «ember-gen» where
  root := `Tests.Ember.Drivers.GenMain

lean_exe «ember-z80» where
  root := `Tests.Ember.Drivers.Z80Main
