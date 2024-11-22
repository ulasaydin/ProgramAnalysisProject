FROM python:3.9-bookworm

RUN useradd -m vscode

RUN python3 -m pip install --upgrade \
    setuptools==69.0.3 \
    gitpython==3.1.41

COPY requirements.txt /tmp/pip-tmp/

RUN pip3 --disable-pip-version-check --no-cache-dir install -r /tmp/pip-tmp/requirements.txt \
   && rm -rf /tmp/pip-tmp
