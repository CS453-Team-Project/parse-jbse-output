import sys
import pytest
import os

curr_dir = os.getcwd()
sys.path.insert(1, os.path.join(curr_dir, "src"))

from main import main

NUM_MODELS = 10


def test1_1():
    with open(os.path.join(curr_dir, "examples/1/methods.txt"), "r") as f:
        methods = [r.strip() for r in f.readlines()]
    path, s, r, models = main(
        os.path.join(curr_dir, "examples/1/path1.txt"),
        methods,
        NUM_MODELS,
    )
    assert len(models) == 1


def test1_2():
    with open(os.path.join(curr_dir, "examples/1/methods.txt"), "r") as f:
        methods = [r.strip() for r in f.readlines()]
    path, s, r, models = main(
        os.path.join(curr_dir, "examples/1/path2.txt"),
        methods,
        NUM_MODELS,
    )
    assert len(models) == NUM_MODELS


def test1_3():
    with open(os.path.join(curr_dir, "examples/1/methods.txt"), "r") as f:
        methods = [r.strip() for r in f.readlines()]
    path, s, r, models = main(
        os.path.join(curr_dir, "examples/1/path3.txt"),
        methods,
        NUM_MODELS,
    )
    assert len(models) == NUM_MODELS


def test1_4():
    with open(os.path.join(curr_dir, "examples/1/methods.txt"), "r") as f:
        methods = [r.strip() for r in f.readlines()]
    path, s, r, models = main(
        os.path.join(curr_dir, "examples/1/path4.txt"),
        methods,
        NUM_MODELS,
    )
    # There are no parameters to set, to `models` is equivalent to [([], [])]
    assert len(models) == 1


def test2_1():
    with open(os.path.join(curr_dir, "examples/2/methods.txt"), "r") as f:
        methods = [r.strip() for r in f.readlines()]
    path, s, r, models = main(
        os.path.join(curr_dir, "examples/2/path1.txt"),
        methods,
        NUM_MODELS,
    )
    # {V0} > 0.0d can be satisfied by many models
    assert len(models) == NUM_MODELS


def test2_2():
    with open(os.path.join(curr_dir, "examples/2/methods.txt"), "r") as f:
        methods = [r.strip() for r in f.readlines()]
    path, s, r, models = main(
        os.path.join(curr_dir, "examples/2/path2.txt"),
        methods,
        NUM_MODELS,
    )
    # {V0} < 0.0d can be satisfied by many models
    assert len(models) == NUM_MODELS


def test2_3():
    with open(os.path.join(curr_dir, "examples/2/methods.txt"), "r") as f:
        methods = [r.strip() for r in f.readlines()]
    path, s, r, models = main(
        os.path.join(curr_dir, "examples/2/path3.txt"),
        methods,
        NUM_MODELS,
    )
    # {V0} == 0.0d can be satisfied by only 1 model
    assert len(models) == 1
