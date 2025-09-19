import pytest
from simulation.controller import LevelCrossingController, State

def test_train_detection():
    controller = LevelCrossingController()
    assert controller.detect_train(250) is True
    assert controller.detect_train(50) is False

def test_fail_safe():
    controller = LevelCrossingController()
    controller.state = State.FAIL_SAFE
    controller.update(train_x=250)
    assert controller.barrier_down is True
