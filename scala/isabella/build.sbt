name := "isabella"
version := "0.1.0"
scalaVersion := "3.4.0"

// Isabelle-generated code may have style warnings
scalacOptions ++= Seq(
  "-deprecation",
  "-feature",
  "-Wconf:any:silent"  // Suppress warnings for generated code
)

// Source directory structure
Compile / unmanagedSourceDirectories += baseDirectory.value / "src"
