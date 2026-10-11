import LeanChecker

/- Invoke the bundled checker function sequentially to avoid five simultaneous
import environments. This is verification tooling, not a theorem source. -/
#eval do
  for target in ["Kantorovich", "Kantorovich.Stability",
      "Kantorovich.ThreeCertificates", "Kantorovich.ThreeStability",
      "Kantorovich.Examples"] do
    IO.println s!"sequentially replaying {target}"
    replayFromImports target.toName
