# HAPM

Held-out adjusted plus-minus (HAPM) for every NBA player since 1997-98, from LUMA Basketball Research.

Site: https://lumahoops.github.io/hapm/

HAPM is the points per 100 possessions a player's stints produced above what the other nine players were expected to
produce with an average player in his place. The other nine are rated without any of his possessions, starting from
their three previous seasons.

The page shows HAPM, offense and defense by season or range of seasons, with filters for version, position, team and
possessions, and a team view. Shot value (selection, conversion, by zone) and possession value (generation, retention)
are available for versions 1/3 and 2/3.

## Data
- `data/<season>.csv`: one row per player and version for that season. Columns are described in
  [lumahoops/NBA `SCHEMA.md`](https://github.com/lumahoops/NBA/blob/main/SCHEMA.md).
- The frozen, hashed release is in [lumahoops/NBA `hapm/`](https://github.com/lumahoops/NBA/tree/main/hapm).

The files hold model outputs only. The model code, settings and inputs are not included.

## License and credit
Data: CC BY 4.0 (`LICENSE`). Credit: LUMA Basketball Research, with a link to https://lumahoops.github.io/hapm/.
The license covers the published numbers; it does not license the model or its method.

© 2026 Court Share LLC
