#I "packages/FAKE/tools"
#r "packages/FAKE/tools/FakeLib.dll"

open Fake

// Dirs

let tempDir = "./temp"
let srcDir = tempDir + "/src"

// Clean

Target "Clean" (fun _ ->
    CleanDirs [ tempDir ])

// Build

Target "Build" (fun _ ->
    !! "src/**/*.fsproj"
    |> MSBuildRelease srcDir "Build"
    |> Log "Build Source: ")

// Publish

Target "Publish" (fun _ ->
    NuGet (fun p ->
        { p with
              Authors = [ "Andrew Cherry" ]
              Project = "Hekate"
              OutputPath = tempDir
              WorkingDir = srcDir
              Version = "1.0.1"
              AccessKey = getBuildParamOrDefault "nuget_key" ""
              Publish = hasBuildParam "nuget_key"
              Dependencies =
                [ "Aether", GetPackageVersion "packages" "Aether" ]
              Files = 
                [ "Hekate.dll", Some "lib/net40", None
                  "Hekate.pdb", Some "lib/net40", None
                  "Hekate.xml", Some "lib/net40", None ] })
              "./nuget/Hekate.nuspec")

// Dependencies

"Clean"
    ==> "Build"
    ==> "Publish"

RunTargetOrDefault "Publish"
