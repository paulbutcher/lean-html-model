/-
Copyright (c) 2026 Paul Butcher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import Lake
open Lake DSL

package «html-model» where
  version := v!"0.1.1"
  leanOptions := #[⟨`warningAsError, true⟩]

require regular from git "https://github.com/paulbutcher/lean-regular" @ "v0.1.0"

@[default_target]
lean_lib HtmlModel

/-- The `test` subproject is deliberately not a dependency of this package, so that
downstream consumers don't inherit test-only tooling. Running it as a child process
keeps `lake test` working from the repo root regardless. -/
@[test_driver]
script tests do
  let child ← IO.Process.spawn { cmd := "lake", args := #["test"], cwd := __dir__ / "test" }
  child.wait
