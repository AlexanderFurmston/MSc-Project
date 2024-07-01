import java.awt.geom.NoninvertibleTransformException
import java.io.{File, InputStreamReader}
import java.util.concurrent.TimeUnit
import TestResult._

object Classifier {

  val TIMEOUT: java.time.Duration = java.time.Duration.ofMinutes(10)

  // Kills konclude by force //
  def destroyKonclude(koncludeProcess: Option[Process]) = {
    if (!koncludeProcess.isEmpty) {
      koncludeProcess.get.destroyForcibly
      if (koncludeProcess.get.isAlive) koncludeProcess.get.waitFor
    }
  }

  // Recovers last line of a child process //
  def lastLine(process: Option[Process]): String = {
    if (process.isEmpty) return ""
    val procInput = new java.io.BufferedReader(new InputStreamReader(process.get.getInputStream))
    var line: String = ""
    var nextLine = procInput.readLine
    while ( nextLine != null) {
      // System.out.println(nextLine.get)
	    // if (nextLine == "NOMINALHAVOC" ) return "havoc"
      line = nextLine
      nextLine = procInput.readLine
    }
    return line
  }



  /**
    * This test takes:
    *
    * A file `file` representing an ontology.
    * A string `reasoner` with the name of a reasoner.
    * A set of options `loadOnly` for a load test, `hashTaxonomy` for hashing the taxonomy, and `writeTaxonomy` for
    *   writing the taxonomy, and `debug` for displaying additional info.
    * A folder `taxonomyFolder` where to save the taxonomy, if necessary.
    *
    * It then asks the file in the string `reasoner` to classify the ontology in `file`, and it outputs a message of the form
    * [SUCCESS/ERROR/TIMEOUT].PreliminaryTest.([HASH].Hash/error information)
    *
    */


  def classify(file: java.io.File, reasoner: String, loadOnly: Boolean, hashTaxonomy: Boolean,
                writeTaxonomy: Boolean, taxonomyFolder: String, debug: Boolean ): TestResult = {

    // Print additional info if debug mode on.
    if (debug) {
      System.out.println("[DEBUG]. Preliminary test parameters: ")
      System.out.println("   ** Input file: " + file.toString)
      System.out.println("   ** Reasoner: " + reasoner)
      System.out.println("   ** Load Only Test?: " + yesno(loadOnly))
      System.out.println("   ** Hash Taxonomy?: " + yesno(hashTaxonomy))
      System.out.println("   ** Write Taxonomy?: " + yesno(writeTaxonomy))
      System.out.println("   ** Folder for saving taxonomy: " + taxonomyFolder)
    }

    // Prepare strings to be sent to the reasoner as input.
    val load: String = if (loadOnly) "load" else ""
    val write: String = if (writeTaxonomy) "write" else ""
    val hash: String = if (hashTaxonomy) "hash" else ""

    // Special preparations for Factpp and Konclude
    //// String with path of Factpp library. This assumes the library is in the same folder as the reasoner.
    val nativeLibAddress: String = if (reasoner.endsWith("factpp.jar")) {" -Djava.library.path=" + reasoner.dropRight(11)} else ""
    //// Create Konclude OWLLink Server. This assumes that Konclude is in the folder /home/davala/ and sets up one thread, and in the port 8080
    val koncludeProcess: Option[Process] = {
      if (reasoner.endsWith("konclude.jar")) {
        try {
          Some(Runtime.getRuntime().exec("/home/davala/Konclude-v0.6.2-544-Linux-x64-GCC4.3.2-Static-Qt4.8.5/Binaries/Konclude owllinkserver -w 1 -p 8080"))
        } catch {
          case _: Throwable => {
            return new TestResult(success = "[FAIL]", message = "Konclude server could not be initialised in preliminary test.")
            None
          }
        }
      } else None
    }
    ////// Give 3 seconds to the Konclude server so that it can initialise. This is always more than enough.
    if (!koncludeProcess.isEmpty) koncludeProcess.get.waitFor(3000,TimeUnit.MILLISECONDS)

    // Execute Subprocess
    val process: Option[Process] = {
      try {
        val command: String = "java -jar " + nativeLibAddress + " " + reasoner + " " + file.toString + " " + taxonomyFolder + " " + load + " " + write + " " + hash + " " + "time"
        if (debug) System.out.println("Executing command: " + command)
        Some(Runtime.getRuntime.exec(command))
      } catch {
        case _: Throwable => {
          destroyKonclude(koncludeProcess)
          return new TestResult(success = "[FAIL]", message = "Command rejected for " + reasoner + " in preliminary test.")
        }
      }
    }

    // Wait until Timeout and Harvest Result
    if (debug) System.out.println("Waiting for command to be completed... ")
    if (!process.isEmpty) {
      process.get.waitFor(TIMEOUT.toMillis, java.util.concurrent.TimeUnit.MILLISECONDS)
      destroyKonclude(koncludeProcess)
      // If process is alive after this time, send kill signal to process, and wait until the process is no more. This is
      // usually a matter of seconds, but can generate problems if we do not wait.
      if (process.get.isAlive()) {
        process.get.destroyForcibly
        process.get.waitFor
        return new TestResult(success = "[SUCCESS]", hash = "---", time = "TIMEOUT" )
      }
      if (debug) System.out.println("Command has been completed.")
      // Recover result of the test.
      // This assumes that the output yielded by the subprocess is not full of debris. The Harnesses are silenced and only
      // print a single line with the test results, so this should not be a problem. No ``debug'' argument is passed to the sub-process, as this
      // would un-silence the subprocess. The harnessOutput... methods already presume sub-proces output will be of a certain way.
      val lastline: String = lastLine(process)
      // if (lastline == "havoc") return "[SUCCESS].PreliminaryTest" + ".[HASH].NOMINALHAVOC"
      val hash: Option[Int] = harnessOutputHash(lastline)
      val time: Option[Int] = harnessOutputTime(lastline)
      val message : String = harnessOutputMessage(lastline)
      val contextCount: Int = harnessOutputContextCount(lastline)
      if (harnessOutputSuccess(lastline)) return new TestResult(success = "[SUCCESS]", hash = hash.getOrElse("---").toString , time = time.getOrElse("---").toString , message = message, contextCount = contextCount)
      else return new TestResult(success = "[FAIL]", message = message)
    }
    // This level should not be reached, and it indicates a bug.
    return new TestResult(success = "[FAIL]", message = "Harness process was started but cannot be found. This is a bug on the test matrix.")
  }

 /**
    * This test takes:
    *
    * A file `file` representing an ontology.
    * A string `reasoner` with the name of a reasoner.
    * An integer ``remaining'' >= 0 with the number of repetitions after this one.
    * An integer ``totalTime'' with the time in all classifications so far.
    * A folder `outputFolder` where to record the result of the test.
    *
    * Then it recursively asks the file in the string `reasoner` to classify the ontology in `file`, one time plus as many as
    * in ``remaining'', and it finially outputs a message of the form
    * [SUCCESS/ERROR/TIMEOUT].PreliminaryTest.([HASH].Hash/error information)
    *
    */

  def reClassify(file: java.io.File, reasoner: String, remaining: Int, totalTime: Int, outputFolder: String, debug: Boolean ): String = {

    assert(remaining >= 0)

    if (debug) {
      System.out.println("[DEBUG]. Timed re-classification: ")
      System.out.println("   ** Input file: " + file.toString)
      System.out.println("   ** Reasoner: " + reasoner)
    }
    val nativeLibAddress: String = if (reasoner.endsWith("factpp.jar")) {" -Djava.library.path=" + reasoner.dropRight(11)} else ""

    // Create Konclude OWLLink Server
    val koncludeProcess: Option[Process] = {
      if (reasoner.endsWith("konclude.jar")) {
        try {
          Some(Runtime.getRuntime().exec("/home/davala/Konclude-v0.6.2-544-Linux-x64-GCC4.3.2-Static-Qt4.8.5/Binaries/Konclude owllinkserver -w 1 -p 8080"))
        } catch {
          case _: Throwable => {
            return "[ERROR].ClassificationLoop.Konclude server could not be initialised"
            None
          }
        }
      } else None
    }
    if (!koncludeProcess.isEmpty) koncludeProcess.get.waitFor(3000,TimeUnit.MILLISECONDS)

    // Execute Harness Test
    val process: Option[Process] = {
      try {
        val command = "java -jar " + nativeLibAddress + " " + reasoner + " " + file.toString + " " + outputFolder + " " + "time"
        if (debug) System.out.println("Executing command: " + command)
        Some(Runtime.getRuntime.exec(command))
      } catch {
        case _: Throwable => {
          destroyKonclude(koncludeProcess)
          return ("[ERROR].ClassificationLoop" + "." +  "Command could not be executed for " + reasoner + " in preliminary test.")
        }
      }
    }
    if (debug) System.out.println("Waiting for command to be completed... ")
    if (!process.isEmpty) {
      process.get.waitFor(TIMEOUT.toMillis, java.util.concurrent.TimeUnit.MILLISECONDS)
      destroyKonclude(koncludeProcess)
      if (process.get.isAlive()) {
        process.get.destroyForcibly
        process.get.waitFor
        return "[TIMEOUT].ClassificationLoop"
      }
      if (debug) System.out.println("Command has been completed.")
      val lastline: String = lastLine(process)
      val time: Option[Int] = harnessOutputTime(lastline)
      if (time.isEmpty) return "[ERROR].ClassificationLoop." + harnessOutputMessage(lastline)
      if (remaining == 0) return ("[SUCCESS].ClassificationLoop." + (totalTime + time.get))
      else return reClassify(file, reasoner, (remaining - 1), (totalTime + time.get), outputFolder,debug)
    }
    return "[ERROR].ClassificationLoop.Harness process has been prematurely destroyed."
  }

  def log(file: java.io.File, reasoner: String, outputBuffer: java.io.BufferedWriter, message: String): Unit = {
     outputBuffer.newLine
     outputBuffer.write(file.toString + "," + reasoner + "," + message)
  }
  
  def yesno(boolean: Boolean): String = { if (boolean) {return "yes"} else {return "no"} }

  def harnessOutputSuccess(line: String): Boolean = {
   try {
     (line.substring(line.indexOfSlice("<success>") + 9, line.indexOfSlice("</success>"))).toBoolean
    } catch {
      case _: Throwable => false
    }
  }

  def harnessOutputTime(line: String): Option[Int] = {
    try {
      Some((line.substring(line.indexOfSlice("<time>") + 6, line.indexOfSlice("</time>"))).toInt)
    } catch {
      case _: Throwable => None
    }
  }

def harnessOutputHash(line: String): Option[Int] = {
    try {
      Some((line.substring(line.indexOfSlice("<hash>") + 6, line.indexOfSlice("</hash>"))).toInt)
    } catch {
      case _: Throwable => None
    }
  }

  def harnessOutputMessage(line: String): String = {
    try {
      line.substring(line.indexOfSlice("<errmsg>") + 8, line.indexOfSlice("</errmsg>"))
    } catch {
      case _: Throwable => ""
    }
  }

  def harnessOutputContextCount(line: String): Int = {
    try {
      (line.substring(line.indexOfSlice("<contextCount>") + 14, line.indexOfSlice("</contextCount>"))).toInt
    } catch {
      case _: Throwable => 0
    }
  }


}



