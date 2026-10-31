# Hummingbird, repackaged with apiPath "/"

The market package's bridge config sets `apiPath = "/tracking_pixel/"`, so an `api` route reaches only the
tracking pixel while the typed declaration (`apps/interfaces/hummingbird.json`) speaks socket.io to the app. This
recipe (`repack.sh`) republishes the same app tree under our own key with `apiPath = "/"`; roles and permissions
(tracker, manager / view-data) are unchanged, and the author's PGP signature, which signs the old app id, is dropped.

- Source package: 9365130605f1998f3d4aea205d8768ae (app 4mfserfc04wtcevvgn0jw27hvwfntmt8j468y3ma55kj8d5tj9kh).
- This package: app `434g078hse54h0tt189hsyp2stf7n7rap8uxwjf3dyq2zvymrx0h`, package `c7287dfbae2796cd283a32452d2395c7`
  (SHA-256 prefix of the file), built on dregg-forge at `/srv/spk-build/hummingbird/out/hummingbird-0.4.1-api.spk`;
  key `/srv/spk-build/hummingbird/hummingbird.key` (0600, not in the repository).
- The build was done by hand with the same steps `repack.sh` encodes (decode, edit, `spk pack`); `spk verify` accepts
  the result. `repack.sh` itself has not been run end to end.
- Not yet qualified live: needs a Hermes controller world with this package attached as a typed application
  (`ar-j14run2.sh`-style j14-apps qualify run, alias hb, role 1 = manager).
