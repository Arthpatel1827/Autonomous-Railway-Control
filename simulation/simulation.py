# import pygame
# import sys
# from simulation.controller import LevelCrossingController, Geometry

# # ---------------- Layout & constants ----------------
# WIDTH, HEIGHT   = 800, 400
# TRACK_Y         = 200                   # horizontal tracks center
# ROAD_X          = 400                   # vertical road x
# BARRIER_Y       = TRACK_Y + 40          # barrier just before tracks (on road)
# TRAIN_W, TRAIN_H = 200, 40
# CAR_W, CAR_H     = 40, 60
# TRAIN_SPEED      = 5
# CAR_SPEED        = 2

# geom = Geometry(road_x=ROAD_X, train_w=TRAIN_W, approach_margin=140)

# # ---------------- Pygame setup ----------------------
# pygame.init()
# screen = pygame.display.set_mode((WIDTH, HEIGHT))
# pygame.display.set_caption("Railway Level Crossing Safety System")
# clock = pygame.time.Clock()
# font = pygame.font.SysFont(None, 36)

# # Colors
# WHITE=(255,255,255); BLACK=(0,0,0); RED=(200,0,0); GREEN=(0,200,0)
# BLUE=(0,0,200); ROAD_GRAY=(210,210,210)

# # ---------------- Simulation state ------------------
# train_x = -TRAIN_W          # train enters from left
# car_y   = HEIGHT - 80       # car starts near bottom, moves up
# ctl     = LevelCrossingController(geom)

# # ---------------- Drawing helpers -------------------
# def draw_tracks():
#     pygame.draw.line(screen, BLACK, (0, TRACK_Y-10), (WIDTH, TRACK_Y-10), 5)
#     pygame.draw.line(screen, BLACK, (0, TRACK_Y+10), (WIDTH, TRACK_Y+10), 5)

# def draw_road():
#     pygame.draw.rect(screen, ROAD_GRAY, (ROAD_X - 35, 0, 70, HEIGHT))
#     pygame.draw.line(screen, BLACK, (ROAD_X-35,0), (ROAD_X-35,HEIGHT), 4)
#     pygame.draw.line(screen, BLACK, (ROAD_X+35,0), (ROAD_X+35,HEIGHT), 4)

# def draw_train(x):
#     pygame.draw.rect(screen, BLUE, (x, TRACK_Y - TRAIN_H//2, TRAIN_W, TRAIN_H))

# def draw_car(y):
#     pygame.draw.rect(screen, GREEN, (ROAD_X - CAR_W//2, y, CAR_W, CAR_H))

# def draw_barrier(down: bool):
#     if down:   # blocking: horizontal arm across road
#         pygame.draw.rect(screen, RED, (ROAD_X - 40, BARRIER_Y, 80, 10))
#     else:      # up: vertical post beside road
#         pygame.draw.rect(screen, RED, (ROAD_X + 45, BARRIER_Y - 40, 10, 80))

# # ---------------- Physics helpers -------------------
# def car_over_tracks(y):
#     top, bot = y, y + CAR_H
#     return not (bot < TRACK_Y - 12 or top > TRACK_Y + 12)

# def car_should_stop(y, barrier_down):
#     stop_line = BARRIER_Y + 12
#     near_barrier = (y + CAR_H) >= stop_line and (y < stop_line + 8)
#     return barrier_down and near_barrier

# def check_collision(train_x, y, barrier_down):
#     # A collision if (train overlaps road) AND (car overlaps track band) AND barrier is NOT blocking.
#     train_crossing = ctl.train_in_crossing_zone(train_x)
#     return (not barrier_down) and train_crossing and car_over_tracks(y)

# # ---------------- Main loop -------------------------
# def run():
#     global train_x, car_y

#     while True:
#         # Events
#         for event in pygame.event.get():
#             if event.type == pygame.QUIT:
#                 pygame.quit(); sys.exit()
#             if event.type == pygame.KEYDOWN:
#                 if event.key == pygame.K_h:
#                     ctl.hazard_mode = not ctl.hazard_mode
#                 if event.key == pygame.K_f:
#                     # toggle fail-safe latch (for demo); auto-clears when clear
#                     ctl.set_fail_safe(not ctl.fail_safe_active)

#         # Background
#         screen.fill(WHITE)
#         draw_road()
#         draw_tracks()

#         # Move train (left -> right; loop)
#         train_x += TRAIN_SPEED
#         if train_x > WIDTH:
#             train_x = -TRAIN_W

#         # Controller update
#         ctl.update(train_x)

#         # Draw train + barrier
#         draw_train(train_x)
#         draw_barrier(ctl.barrier_down)

#         # Move car upward unless blocked at the barrier
#         if not car_should_stop(car_y, ctl.barrier_down):
#             car_y -= CAR_SPEED
#         if car_y + CAR_H < 0:
#             car_y = HEIGHT - 80  # loop car

#         draw_car(car_y)

#         # Status / safety messages
#         if check_collision(train_x, car_y, ctl.barrier_down):
#             msg = font.render("⚠️ COLLISION! Unsafe state!", True, RED)
#         elif ctl.fail_safe_triggered:
#             msg = font.render("Fail-safe: Barriers forced down", True, BLACK)
#             ctl.fail_safe_triggered = False
#         else:
#             msg = font.render("System operating safely", True, BLACK)

#         screen.blit(msg, (WIDTH//2 - msg.get_width()//2, 20))
#         clock.tick(30)
#         pygame.display.flip()

# if __name__ == "__main__":
#     run()
import pygame
import sys
from simulation.controller import LevelCrossingController, Geometry

# ---------------- Layout & constants ----------------
WIDTH, HEIGHT    = 800, 400
TRACK_Y          = 200                   # horizontal tracks center
ROAD_X           = 400                   # vertical road x
BARRIER_Y        = TRACK_Y + 40          # barrier just before tracks (on road)
TRAIN_W, TRAIN_H = 200, 40
CAR_W, CAR_H     = 40, 60

# Speeds are in pixels/second (frame-rate independent)
TRAIN_SPEED_PPS  = 150.0                 # start values; tune live
CAR_SPEED_PPS    = 90.0

# How long before the train reaches the road we want the barrier DOWN
T_CLOSE_SEC      = 1.2                   # pre-closure time budget
SAFETY_BUFFER_PX = 20

# ---------------- Pygame setup ----------------------
pygame.init()
screen = pygame.display.set_mode((WIDTH, HEIGHT))
pygame.display.set_caption("Railway Level Crossing Safety System")
clock = pygame.time.Clock()
font = pygame.font.SysFont(None, 22)
banner_font = pygame.font.SysFont(None, 36)

# Colors
WHITE=(255,255,255); BLACK=(0,0,0); RED=(200,0,0); GREEN=(0,200,0)
BLUE=(0,0,200); ROAD_GRAY=(210,210,210)

# ---------------- Simulation state ------------------
train_x = -TRAIN_W          # train enters from left
car_y   = HEIGHT - 80       # car starts near bottom, moves up

# geometry; approach_margin will be updated each frame from speed
geom = Geometry(road_x=ROAD_X, train_w=TRAIN_W, approach_margin=160)
ctl  = LevelCrossingController(geom)

# ---------------- Drawing helpers -------------------
def draw_tracks():
    pygame.draw.line(screen, BLACK, (0, TRACK_Y-10), (WIDTH, TRACK_Y-10), 5)
    pygame.draw.line(screen, BLACK, (0, TRACK_Y+10), (WIDTH, TRACK_Y+10), 5)

def draw_road():
    pygame.draw.rect(screen, ROAD_GRAY, (ROAD_X - 35, 0, 70, HEIGHT))
    pygame.draw.line(screen, BLACK, (ROAD_X-35,0), (ROAD_X-35,HEIGHT), 4)
    pygame.draw.line(screen, BLACK, (ROAD_X+35,0), (ROAD_X+35,HEIGHT), 4)

def draw_train(x):
    pygame.draw.rect(screen, BLUE, (x, TRACK_Y - TRAIN_H//2, TRAIN_W, TRAIN_H))

def draw_car(y):
    pygame.draw.rect(screen, GREEN, (ROAD_X - CAR_W//2, y, CAR_W, CAR_H))

def draw_barrier(down: bool):
    if down:   # blocking: horizontal arm across road
        pygame.draw.rect(screen, RED, (ROAD_X - 40, BARRIER_Y, 80, 10))
    else:      # up: vertical post beside road
        pygame.draw.rect(screen, RED, (ROAD_X + 45, BARRIER_Y - 40, 10, 80))

def hud(train_speed, car_speed):
    lines = [
        f"Train speed: {train_speed:.0f} px/s  (1/2 to - / +)",
        f"Car speed:   {car_speed:.0f} px/s  (9/0 to - / +)",
        f"'H' hazard mode (barrier fails)  |  'F' toggle fail-safe latch",
        f"Approach margin: {ctl.geom.approach_margin}px  (derived from train speed)"
    ]
    for i, text in enumerate(lines):
        s = font.render(text, True, BLACK)
        screen.blit(s, (8, 8 + i*18))

# ---------------- Physics helpers -------------------
def car_over_tracks(y):
    top, bot = y, y + CAR_H
    return not (bot < TRACK_Y - 12 or top > TRACK_Y + 12)

def car_should_stop(y, barrier_down):
    stop_line = BARRIER_Y + 12
    near_barrier = (y + CAR_H) >= stop_line and (y < stop_line + 8)
    return barrier_down and near_barrier

def check_collision(train_x, y, barrier_down):
    train_crossing = ctl.train_in_crossing_zone(train_x)
    return (not barrier_down) and train_crossing and car_over_tracks(y)

# ---------------- Main loop -------------------------
def run():
    global train_x, car_y, TRAIN_SPEED_PPS, CAR_SPEED_PPS

    while True:
        dt = clock.tick(60) / 1000.0  # seconds since last frame (cap ~60 fps)

        # Events / controls
        for event in pygame.event.get():
            if event.type == pygame.QUIT:
                pygame.quit(); sys.exit()
            if event.type == pygame.KEYDOWN:
                if event.key == pygame.K_h:
                    ctl.hazard_mode = not ctl.hazard_mode
                if event.key == pygame.K_f:
                    ctl.set_fail_safe(not ctl.fail_safe_active)
                # Train speed adjust (1/2 decrease, -/+ increase)
                if event.key in (pygame.K_1, pygame.K_KP1, pygame.K_2, pygame.K_KP2):
                    TRAIN_SPEED_PPS = max(20.0, TRAIN_SPEED_PPS - 10.0)
                if event.key in (pygame.K_MINUS, pygame.K_KP_MINUS):
                    TRAIN_SPEED_PPS = max(20.0, TRAIN_SPEED_PPS - 10.0)
                if event.key in (pygame.K_EQUALS, pygame.K_PLUS, pygame.K_KP_PLUS):
                    TRAIN_SPEED_PPS = min(600.0, TRAIN_SPEED_PPS + 10.0)
                # Car speed adjust (9 decrease, 0 increase)
                if event.key in (pygame.K_9, pygame.K_KP9):
                    CAR_SPEED_PPS = max(10.0, CAR_SPEED_PPS - 10.0)
                if event.key in (pygame.K_0, pygame.K_KP0):
                    CAR_SPEED_PPS = min(400.0, CAR_SPEED_PPS + 10.0)

        # Background
        screen.fill(WHITE)
        draw_road()
        draw_tracks()

        # Derive approach margin from current train speed:
        # we want the barrier down T_CLOSE_SEC before the train reaches the road.
        # margin = distance train travels in T_CLOSE_SEC + a small buffer.
        ctl.geom.approach_margin = int(TRAIN_SPEED_PPS * T_CLOSE_SEC + SAFETY_BUFFER_PX)

        # Move train (left -> right; loop)
        train_x += TRAIN_SPEED_PPS * dt
        if train_x > WIDTH:
            train_x = -TRAIN_W

        # Controller update
        ctl.update(int(train_x))  # pass int for geometry comparisons

        # Draw train + barrier
        draw_train(int(train_x))
        draw_barrier(ctl.barrier_down)

        # Move car upward unless blocked at the barrier
        if not car_should_stop(car_y, ctl.barrier_down):
            car_y -= CAR_SPEED_PPS * dt
        if car_y + CAR_H < 0:
            car_y = HEIGHT - 80  # loop car

        draw_car(int(car_y))

        # Status banner
        if check_collision(int(train_x), int(car_y), ctl.barrier_down):
            banner = banner_font.render("⚠️ COLLISION! Unsafe state!", True, RED)
        elif ctl.fail_safe_triggered:
            banner = banner_font.render("Fail-safe: Barriers forced down", True, BLACK)
            ctl.fail_safe_triggered = False
        else:
            banner = banner_font.render("System operating safely", True, BLACK)
        screen.blit(banner, (WIDTH//2 - banner.get_width()//2, 20))

        # HUD with live values
        hud(TRAIN_SPEED_PPS, CAR_SPEED_PPS)

        pygame.display.flip()

if __name__ == "__main__":
    run()
