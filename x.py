#!/usr/bin/env python3

"""A wrapper for cargo that sets up the correct environment."""

import sys
if sys.version_info[0] < 3:
    print('You need to run this script with Python 3.')
    sys.exit(1)

import os
import subprocess

verbose = False
dry_run = False


def report(template, *args, **kwargs):
    """Print the message if `verbose` is `True`."""
    if verbose:
        print(template.format(*args, **kwargs))


def error(template, *args, **kwargs):
    """Print the error and exit the program."""
    print(template.format(*args, **kwargs))
    sys.exit(1)


def run_command(args, env=None):
    """Run a command with the given arguments."""
    if env is None:
        env = os.environ.copy()
    completed = subprocess.run(args, env=env)
    if completed.returncode != 0:
        sys.exit(completed.returncode)


def shell(command, term_on_nzec=True):
    """Run a shell command."""
    print("Running a shell command: ", command)
    if not dry_run:
        completed = subprocess.run(command.split())
        if completed.returncode != 0 and term_on_nzec:
            sys.exit(completed.returncode)
        return completed.returncode


def cargo(args):
    """Run cargo with the given arguments."""
    run_command(['cargo'] + args)


def setup_rustup():
    # Setup rustc components.
    shell('rustup component add rustc-dev')
    shell('rustup component add llvm-tools-preview')


def setup(args):
    """Install the dependencies."""
    if len(args) == 1 and args[0] == '--dry-run':
        global dry_run
        dry_run = True
    elif args:
        error("unexpected arguments: {}", args)
    setup_rustup()


def main(argv):
    global verbose
    for i, arg in enumerate(argv):
        if arg.startswith('+'):
            if arg == '+v' or arg == '++verbose':
                verbose = True
                continue
            else:
                error('unknown option: {}', arg)
        elif arg == 'setup':
            setup(argv[i+1:])
            break
        else:
            cargo(argv[i:])
            break
    if not argv:
        cargo(argv)


if __name__ == '__main__':
    main(sys.argv[1:])
