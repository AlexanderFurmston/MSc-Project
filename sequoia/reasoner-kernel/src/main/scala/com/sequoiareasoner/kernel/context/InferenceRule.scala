package com.sequoiareasoner.kernel.context.inferenceRule

/** ----------------------------- TYPES OF RULES -------------------------------------------- */

sealed trait InferenceRule
case object Core extends InferenceRule
case object Hyper extends InferenceRule
case object PossibleGroundFact extends InferenceRule
case object Nom extends InferenceRule
case object Succ extends InferenceRule
case object Pred extends InferenceRule
case object Query extends InferenceRule
case object Eq extends InferenceRule
case object Coll extends InferenceRule
case object ABox extends InferenceRule
case object CertainGroundClause extends InferenceRule
