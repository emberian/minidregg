# 0.6.9-1

- Built from the maintained Sandstorm fork at commit `ba4d72ef` (ot-recorder 0.6.9) on Debian 13, signed with a new application key.
- The Sandstorm identity header is percent-decoded and reduced to the recorder's own storage name before it is used, so a location written by one signed-in user is found again by the lookup for that user. Before this, `Grain%20owner` was stored as `grain-20owner` but looked up as `grain%20owner`.
- The package API path is `/`, so the installed descriptor exports an `api` interface beside `web`.
