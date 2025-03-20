
- Check that:
    * `make` run in the `Coq/` folder doesn't return an error
    * `Generation.sh` feeds the `Articles/` folder

- If the logo isn't present in the production server (web host),
    * if it's not generated yet in development environment (your PC), run `DrawLogo.py`
    * feed in production the `Images/` folder with `Logo.png`

- Copy into production:
    * `index.html`
    * `Templates/general.css`
    * All the files of `Articles/`

- `git push`
