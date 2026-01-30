import GameTheory.EuclideanGames
import GameTheory.EuclideanNashExistence

-- Check axioms used by our proven lemmas
#print axioms EuclideanStrategicGame.actionProfileSet_nonempty
#print axioms EuclideanStrategicGame.actionProfileSet_convex
#print axioms EuclideanStrategicGame.actionProfileSet_isCompact
#print axioms EuclideanStrategicGame.best_response_set_nonempty
#print axioms EuclideanStrategicGame.best_response_set_convex
#print axioms EuclideanStrategicGame.BR_nonempty
#print axioms EuclideanStrategicGame.BR_convex

-- Note: proposition_20_3 has a sorry, so checking axioms would include sorryAx
-- But we can check the parts that are complete
