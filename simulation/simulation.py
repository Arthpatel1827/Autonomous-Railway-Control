import pygame
import sys
from simulation.controller import LevelCrossingController

pygame.init()
WIDTH, HEIGHT = 800, 400
screen = pygame.display.set_mode((WIDTH, HEIGHT))
pygame.display.set_caption("Railway Level Crossing Safety System")

clock = pygame.time.Clock()
font = pygame.font.SysFont(None, 36)

# Colors
WHITE = (255, 255, 255)
BLACK = (0, 0, 0)
RED = (200, 0, 0)
GREEN = (0, 200, 0)
BLUE = (0, 0, 200)

# Train
train_x = -200
train_speed = 5

# Car
car_x = 600
car_speed = 2

# Controller
controller = LevelCrossingController()

# Draw Functions
def draw_train(x):
    pygame.draw.rect(screen, BLUE, (x, 150, 200, 50))


def draw_car(x):
    pygame.draw.rect(screen, GREEN, (x, 280, 60, 30))


def draw_barrier(down):
    if down:
        pygame.draw.rect(screen, RED, (380, 230, 10, 60))  # barrier down
    else:
        pygame.draw.rect(screen, RED, (380, 200, 60, 10))  # barrier up


def check_collision(train_x, car_x, barrier_down):
    """Detect unsafe collision"""
    if 300 < car_x < 400 and 200 < train_x < 400 and not barrier_down:
        return True
    return False


# Simulation Loop
def run():
    global train_x, car_x
    while True:
        for event in pygame.event.get():
            if event.type == pygame.QUIT:
                pygame.quit()
                sys.exit()
            # Toggle hazard mode (H key)
            if event.type == pygame.KEYDOWN:
                if event.key == pygame.K_h:
                    controller.hazard_mode = not controller.hazard_mode

        screen.fill(WHITE)

        # Move train
        train_x += train_speed
        if train_x > WIDTH:
            train_x = -200  # Reset

        # Update FSM
        controller.update(train_x)

        # Draw train + barrier
        draw_train(train_x)
        draw_barrier(controller.barrier_down)

        # Move/draw car
        if controller.barrier_down and 300 < car_x < 400:
            car_speed_now = 0
        else:
            car_speed_now = car_speed

        car_x -= car_speed_now
        if car_x < -100:
            car_x = 600  # Reset

        draw_car(car_x)

        # Road + Tracks
        pygame.draw.line(screen, BLACK, (0, 300), (800, 300), 5)  # road
        pygame.draw.line(screen, BLACK, (0, 200), (800, 200), 5)  # railway

        # Safety messages
        collision = check_collision(train_x, car_x, controller.barrier_down)
        if collision:
            msg = font.render("⚠️ COLLISION! Unsafe state!", True, RED)
            screen.blit(msg, (200, 50))
        elif controller.fail_safe_triggered:
            msg = font.render("Fail-safe: Barriers forced down", True, BLACK)
            screen.blit(msg, (200, 50))
            controller.fail_safe_triggered = False  # reset display
        else:
            msg = font.render("System operating safely", True, BLACK)
            screen.blit(msg, (200, 50))

        pygame.display.flip()
        clock.tick(30)
