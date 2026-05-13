Repository of the website [leibnizproject.com](https://leibnizproject.com)

## Upgrade Lean 4

- `cd Lean4/`
- `lake --version`
- `lake update`
- `lake --version`
- `lake build` and maybe fix compilation errors (commit if so)
- restart Visual Studio Code
- tag the commit with the version number (with a right click on it in gitk for example)

## Upgrade Rocq

- `cd Rocq/`
- `opam update`
- `opam upgrade` (should take a while)
- `make` and maybe fix compilation errors (commit if so)
- restart Visual Studio Code
- tag the commit with the version number (with a right click on it in gitk for example)
