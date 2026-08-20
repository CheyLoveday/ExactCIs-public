# JSS package-paper replication

This directory reproduces the numerical examples in the JSS software-paper
draft for the immutable public release `exactcis==1.1.2` (`v1.1.2`,
`f0cbf3c0ab37ea9a7f96e1b70367f40b6281f3c4`). It uses only the stable public
API and contains no private-repository data.

Run it from a clean environment outside the source checkout:

```bash
python -m venv /tmp/exactcis-jss-venv
/tmp/exactcis-jss-venv/bin/python -m pip install exactcis==1.1.2
/tmp/exactcis-jss-venv/bin/python \
  replication/jss_package_paper.py --mode minimal --show-env
```

The command writes:

- `replication/output/jss/results.json`: canonical deterministic scientific
  outputs;
- `replication/output/jss/env.json`: interpreter, platform, package version,
  import path, and elapsed time;
- `replication/output/jss/manifest.json`: hashes, command, release authority,
  and claim ceiling.

`env.json` records `exactcis.__file__` and whether that path is inside this
checkout. Reviewers should reject a run that reports another package version
or an unintended editable checkout. Environment bytes vary across machines;
`results.json` is the cross-platform scientific comparison artifact.

The minimal run is deterministic, makes no network calls after installation,
uses no random sampling, and is expected to finish in under one hour on an
ordinary computer. The script refuses any installed version other than 1.1.2.
