# ===================== Layout & constants =====================
WIDTH, HEIGHT = 1800, 900

# Two horizontal tracks (top & bottom)
TRACK_Y_TOP = 262
TRACK_Y_BOT = 338
TRACKS = (TRACK_Y_TOP, TRACK_Y_BOT)

# Road centered horizontally
ROAD_X = WIDTH // 2
ROAD_HALF = 120              # half width of paved road (6 lanes total)
POST_CLEAR = 12              # gate posts sit this far OUTSIDE the road edge

# --- Barriers: posts OUTSIDE the road ---
BARRIER_OFFSET = 70          # distance from nearest track center to the gate line
BARRIER_Y_NORTH = TRACK_Y_TOP - BARRIER_OFFSET
BARRIER_Y_SOUTH = TRACK_Y_BOT + BARRIER_OFFSET

TRAIN_W, TRAIN_H = 240, 56
CAR_W, CAR_H     = 46, 70

# Speeds (pixels/second)
TRAIN_SPEED_PPS = 170.0
CAR_SPEED_PPS   = 140.0

# Train arrival randomness (seconds)
TRAIN_GAP_MIN = 2.5
TRAIN_GAP_MAX = 6.0

# ---- Cars: 6 lanes & random spawn gaps ----
NUM_LANES = 6
LANE_W = (2 * ROAD_HALF) / NUM_LANES
LANE_CENTERS = [ROAD_X - ROAD_HALF + (i + 0.5) * LANE_W for i in range(NUM_LANES)]
UP_LANES_X   = LANE_CENTERS[0:3]  # left 3 lanes go UP (northbound, dir=-1)
DOWN_LANES_X = LANE_CENTERS[3:6]  # right 3 lanes go DOWN (southbound, dir=+1)

CAR_GAP_MIN = 0.5
CAR_GAP_MAX = 2.0
MAX_CARS    = 60
MIN_HEADWAY_PX = 60

# Barrier (visual)
BARRIER_LEN        = ROAD_HALF - 8     # arm reaches into road from the post
BARRIER_DOWN_ANG   = 0
BARRIER_UP_ANG     = 80
BARRIER_SWING_DPS  = 180

# Flashing lights
FLASH_HZ = 1.2

# Sensors (A left, B right)
SENSOR_OFFSET = 850
SENSOR_A_X    = ROAD_X - SENSOR_OFFSET
SENSOR_B_X    = ROAD_X + SENSOR_OFFSET

# Stop lines (entry barriers):
#  • UP cars stop just BEFORE the SOUTH entry gate line (C).
#  • DOWN cars stop just BEFORE the NORTH entry gate line (B).
STOP_LINE_UP   = BARRIER_Y_SOUTH + 10                       # entry from south (C)
STOP_LINE_DOWN = BARRIER_Y_NORTH - CAR_H - 10               # entry from north (B)
STOP_EPS = 0.5

# Colors
SKY=(225,240,255); GROUND=(210,225,210); ROAD_ASP=(210,210,210)
RAIL=(35,35,35); SLEEPER=(120,85,60)
WHITE=(255,255,255); BLACK=(0,0,0); RED=(205,40,40); RED_DARK=(160,20,20)
GREEN=(40,180,70); GREEN_D=(35,140,55); BLUE=(40,80,210)
YELLOW=(250,220,70); ORANGE=(255,160,60)
