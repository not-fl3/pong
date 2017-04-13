module Main

import UI.Curses
import System

Width : Nat
Width = 50

Height : Nat
Height = 20

data Direction : (max_width : Nat) -> Type where
  Forward : Direction max_width
  Backward : Direction max_width

data BallAxis : (bound : Nat) -> Type where
   MkBallAxis : (n : Nat) -> Direction bound -> {auto pn : LTE n bound}  -> BallAxis bound

data Ball : Type where
   MkBall : BallAxis Width -> BallAxis Height -> Ball

data Platform = MkPlatform Nat

data PongWorld = MkWorld Platform Platform Ball

defaultWorld : PongWorld
defaultWorld = MkWorld leftPlatform rightPlatform ball where
  ball = MkBall (MkBallAxis 8 Backward) (MkBallAxis 1 Backward)
  leftPlatform = MkPlatform 3
  rightPlatform = MkPlatform 3
  
total
flipDirection : Direction a -> Direction a
flipDirection Forward = Backward
flipDirection Backward = Forward

total
changeDirection : Ball -> Ball
changeDirection (MkBall (MkBallAxis x dx) (MkBallAxis y dy)) =
  case (x == 0 || x == Width, y == 0 || y == Height) of
    (True, False) => MkBall (MkBallAxis x  (flipDirection dx)) (MkBallAxis y dy)
    (False, True) => MkBall (MkBallAxis x dx) (MkBallAxis y (flipDirection dy))
    (True, True) => MkBall (MkBallAxis x (flipDirection dx)) (MkBallAxis y (flipDirection dy))
    otherwise => MkBall (MkBallAxis x dx) (MkBallAxis y dy)

total
applyAxis : BallAxis bound -> BallAxis bound
applyAxis (MkBallAxis Z Backward) = MkBallAxis Z Backward
applyAxis (MkBallAxis (S x) {pn = gte} Backward)  = MkBallAxis x Backward {pn = lteSuccLeft gte}
applyAxis (MkBallAxis x {pn = pn_gte} Forward)  =
  case isLTE (x + 1) bound of
    Yes prf => MkBallAxis (x + 1) Forward {pn = prf}
    No => MkBallAxis x Forward

total
moveBall : Ball -> Ball
moveBall (MkBall x y) = MkBall (applyAxis x) (applyAxis y)

partial
step : PongWorld -> IO ()
step w@(MkWorld left right ball@(MkBall (MkBallAxis x dx) (MkBallAxis y dy))) =
  do
    clear
    move (toIntNat y) (toIntNat x)
    addStr "*"
    refresh
    usleep 100000
    step $ MkWorld left right $ (moveBall . changeDirection) $ ball

partial
main : IO ()
main = do
  startCurses WaitForever
  cursSet Invisible
  step $ defaultWorld
  endWin

-- Local Variables:
-- idris-load-packages: ("curses")
-- End:
