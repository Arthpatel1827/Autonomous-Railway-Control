from enum import Enum, auto
import random


class State(Enum):
    IDLE = auto()
    TRAIN_APPROACHING = auto()
    BARRIER_DOWN = auto()
    CLEAR = auto()
    FAIL_SAFE = auto()


class LevelCrossingController:
    def __init__(self):
        self.state = State.IDLE
        self.barrier_down = False
        self.fail_safe_triggered = False
        self.hazard_mode = False  # if True, simulate barrier failure

    def detect_train(self, train_x):
        """Detect if train is near crossing"""
        return 200 < train_x < 400

    def sensor_failure(self):
        """10% chance of sensor failing"""
        return random.random() < 0.1

    def update(self, train_x):
        """Update the FSM based on train position and failures"""

        # Fail-safe check
        if self.sensor_failure():
            self.state = State.FAIL_SAFE

        if self.state == State.IDLE:
            if self.detect_train(train_x):
                self.state = State.TRAIN_APPROACHING

        elif self.state == State.TRAIN_APPROACHING:
            if not self.hazard_mode:
                self.barrier_down = True
            else:  # hazard mode: barrier fails
                self.barrier_down = False
            self.state = State.BARRIER_DOWN

        elif self.state == State.BARRIER_DOWN:
            if not self.detect_train(train_x):
                self.state = State.CLEAR

        elif self.state == State.CLEAR:
            self.barrier_down = False
            self.state = State.IDLE

        elif self.state == State.FAIL_SAFE:
            self.barrier_down = True
            self.fail_safe_triggered = True
            # After triggering fail-safe, reset
            self.state = State.IDLE
