@0xb7d3c1e9a5f20486;

using Spk = import "/sandstorm/package.capnp";

const pkgdef :Spk.PackageDefinition = (
  id = "OWNTRACKS_APP_ID",
  manifest = (
    appTitle = (defaultText = "OwnTracks"),
    appVersion = 6,
    appMarketingVersion = (defaultText = embed "version.txt"),
    actions = [
      (title = (defaultText = "New Location Log"), nounPhrase = (defaultText = "location log"), command = .myCommand)
    ],
    continueCommand = .myCommand,
    metadata = (
      icons = (appGrid = .logo, grain = .logo, market = .logo, marketBig = .logo),
      website = "https://owntracks.org",
      codeUrl = "https://github.com/mnutt/owntracks-recorder",
      license = (openSource = gpl2, notices = (defaultText = embed "notices.txt")),
      categories = [other],
      author = (upstreamAuthor = "OwnTracks Team"),
      description = (defaultText = embed "description.md"),
      shortDescription = (defaultText = "Location tracker"),
      changeLog = (defaultText = embed "changelog.md"),
    ),
  ),
  sourceMap = (searchPath = [(sourcePath = "rootfs")]),
  fileList = "sandstorm-files.list",
  alwaysInclude = ["opt/app", "usr", "etc", "bin", "lib", "lib64", "sandstorm-http-bridge"],
  bridgeConfig = (apiPath = "/"),
);

const logo :Spk.Metadata.Icon = (svg = embed "logo.svg");

const myCommand :Spk.Manifest.Command = (
  argv = ["/sandstorm-http-bridge", "8000", "--", "/bin/bash", "/opt/app/launcher.sh"],
  environ = [
    (key = "PATH", value = "/usr/local/bin:/usr/bin:/bin"),
    (key = "HOME", value = "/var"),
    (key = "SANDSTORM", value = "1"),
    (key = "TMPDIR", value = "/var/tmp")
  ]
);
