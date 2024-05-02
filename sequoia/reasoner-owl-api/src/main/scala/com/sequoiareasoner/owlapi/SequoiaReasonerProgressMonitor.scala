/*
 * DO NOT ALTER OR REMOVE COPYRIGHT NOTICES OR THIS FILE HEADER.
 *
 * This file is part of Sequoia, an OWL 2 reasoner that supports the SRIQ subset of OWL 2 DL.
 * Copyright 2017 by Andrew Bate <code@andrewbate.com>.
 *
 * This code is free software: you can redistribute it and/or modify
 * it under the terms of the GNU General Public License version 3 only,
 * as published by the Free Software Foundation.
 *
 * This program is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU General Public License version 3 for more details (a copy is
 * included in the LICENSE file that accompanied this code).
 *
 * You should have received a copy of the GNU General Public License
 * version 3 along with this work.  If not, see <http://www.gnu.org/licenses/>.
 */

/*
 * This file is available under and governed by the GNU General Public
 * License version 3 only, as published by the Free Software Foundation.
 * However, the following notice accompanied the original version of this
 * file:
 *
 * Copyright (c) 2016, Andrew Bate, University of Oxford <andrew.bate@cs.ox.ac.uk>.
 * All rights reserved.
 *
 * Redistribution and use in source and binary forms, with or without
 * modification, are permitted provided that the following conditions are met:
 *     * Redistributions of source code must retain the above copyright
 *       notice, this list of conditions and the following disclaimer.
 *     * Redistributions in binary form must reproduce the above copyright
 *       notice, this list of conditions and the following disclaimer in the
 *       documentation and/or other materials provided with the distribution.
 *     * Neither the name of the copyright holder nor the names of its contributors
 *       may be used to endorse or promote products derived from this software
 *       without specific prior written permission.
 *
 * THIS SOFTWARE IS PROVIDED BY THE COPYRIGHT HOLDER AND CONTRIBUTORS "AS IS" AND
 * ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT LIMITED TO, THE IMPLIED
 * WARRANTIES OF MERCHANTABILITY AND FITNESS FOR A PARTICULAR PURPOSE ARE
 * DISCLAIMED. IN NO EVENT SHALL THE COPYRIGHT HOLDER OR CONTRIBUTORS BE LIABLE FOR
 * ANY DIRECT, INDIRECT, INCIDENTAL, SPECIAL, EXEMPLARY, OR CONSEQUENTIAL DAMAGES
 * (INCLUDING, BUT NOT LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS OR SERVICES;
 * LOSS OF USE, DATA, OR PROFITS; OR BUSINESS INTERRUPTION) HOWEVER CAUSED AND
 * ON ANY THEORY OF LIABILITY, WHETHER IN CONTRACT, STRICT LIABILITY, OR TORT
 * (INCLUDING NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT OF THE USE OF THIS
 * SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF SUCH DAMAGE.
 */

package com.sequoiareasoner.owlapi

import com.sequoiareasoner.kernel.reasoner.ProgressMonitor
import org.semanticweb.owlapi.reasoner.{NullReasonerProgressMonitor, ReasonerProgressMonitor}

object SequoiaReasonerProgressMonitor {
  private final val updateInterval = 10
  private final val minimalIncrement = 0.005
}

/** Wrapper of the OWL API [[org.semanticweb.owlapi.reasoner.ReasonerProgressMonitor]] for the
  * [[ProgressMonitor]] interface.
  *
  * @author Andrew Bate <code@andrewbate.com>
  */
class SequoiaReasonerProgressMonitor(underlying: ReasonerProgressMonitor = new NullReasonerProgressMonitor) extends ProgressMonitor {
  require(underlying ne null)

  private[this] var lastUpdateTime: Long = _
  private[this] var lastProgress: Double = _

  override def start(taskDescription: String): Unit = {
    underlying.reasonerTaskStarted(taskDescription)
    lastProgress = 0
    lastUpdateTime = System.currentTimeMillis
  }

  override def report(state: Int, maxState: Int): Unit = {
    val time = System.currentTimeMillis
    val progress: Double = if (maxState == 0) 0 else state.toDouble / maxState.toDouble
    if (time > lastUpdateTime + SequoiaReasonerProgressMonitor.updateInterval && progress > lastProgress + SequoiaReasonerProgressMonitor.minimalIncrement) {
      underlying.reasonerTaskProgressChanged(state, maxState)
      lastUpdateTime = time
      lastProgress = progress
    }
  }

  override def finish: Unit = underlying.reasonerTaskStopped

  def getReasonerProgressMonitor: ReasonerProgressMonitor = underlying

  override def toString: String = s"SequoiaReasonerProgressMonitor[underlying = ${getClass.getSimpleName}]"

}
