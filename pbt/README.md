## Development

### Dependencies

- [pyenv](https://github.com/pyenv/pyenv) should be used to manage local Python versions. It can be installed with e.g. `brew install pyenv` (Linux and Windows users should check instructions).
- [Poetry](https://github.com/python-poetry/poetry) is used to manage dependencies and packaging. See the [github](https://github.com/python-poetry/poetry) page for instructions.

### Python version

The Python version used is `3.9.9`.

### Packaging

To publish a new release increment the version in `pyproject.toml`.

Then

```bash
poetry build;
poetry publish; # requires credentials
```

### Usage

Please see [usage](./samples/usage.md).

### Setting up a workstation

1. Install `pyenv`
2. Install `poetry`
3. Clone this repo
4. `cd <repo>`
5. `pyenv install 3.9.9`
6. `poetry env use python`
7. `poetry shell`
8. `poetry install`
9. `code .` to open a VSCode instance with a Python 3.9.9 interpreter (assuming VSCode)

### Useful commands

With Poetry installed run `poetry install`. Then

- Run the cli program: `poetry run pbt <args>` (entrypoint is `pbt/cli:cli`)
- Tests: `poetry run pytest` or use your code editor. VSCode has built in support.
- Tests with coverage: `poetry run pytest --cov=pbt tests/`
- Tests with Coverage: `poetry run coverage run -m pytest` ([reference](https://hypothesis.readthedocs.io/en/latest/strategies.html?highlight=coverage#interaction-with-pytest-cov))
- Tests with logging output to terminal: `poetry run pytest --log-cli-level=debug`
- Specific test: `poetry run pytest tests/<dir>/<filename>.py -k 'test_<suffix>'`
- Specific test and display stdout: `poetry run pytest tests/<dir>/<filename>.py -s -k 'test_<suffix>'`
- Specific test and display logs: `poetry run pytest tests/<dir>/<filename>.py --log-cli-level=debug -k 'test_<suffix>'`
- Run the pre-commit hooks: `pre-commit run --all-files`
- Run linter manually: `flake8 .`
- Run formatter manually: `black .`
- Run static type checker: `mypy .`
- Sort imports `isort .`

### VSCode Tips

VSCode has solid support for Python development using Poetry. If VSCode does not pick up on Poetry then try navigating to this directory and executing

```bash
poetry shell;
code .;
```

Ensure that the bottom left of your VSCode window shows that you are using the correct Python environment.
