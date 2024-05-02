package com.sequoiareasoner.kernel.context

import com.sequoiareasoner.kernel.clauses.Literal

import scala.collection.mutable


/** Triggers that can trigger a particular rule, and a counter for number of occurrences. */
class TriggerSet[L <: Literal] {

    /** Simple implementation of a counter */
    private[this] class Counter {
      private[this] var count = 0

      def nonZero: Boolean = count > 0

      def increment(): Unit = count += 1

      def decrement(): Unit = {
        count -= 1
        if (count < 0) throw new AssertionError

      }
    }

    /** A counter for each of the triggers of a particular kind */
    private[this] val triggerCounter = new mutable.AnyRefMap[L,Counter]
    /** Trigger occurrences that have already been pushed into the relevant context. */
    private[this] val pushedTriggers = new mutable.HashSet[L]

    def incTriggerCount(literal: L): Unit = triggerCounter.getOrElseUpdate(literal, new Counter).increment()
    def decTriggerCount(literal: L): Unit = triggerCounter(literal).decrement()
    // TODO: if a literal is no longer relevant for the corresponding rule, then retract from successor to optimize the complementary rule.
    def forEachNewTrigger(f: L => Unit): Unit =
      for ((literal, counter) <- triggerCounter) if (counter.nonZero && pushedTriggers.add(literal)) f(literal)

    def clear {
      triggerCounter.clear()

    }

}

