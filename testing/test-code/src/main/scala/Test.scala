import Addresses._
import Classifier._
import TestResult._
import test.InputReader._
import java.lang.Math.floorMod
import java.util.Calendar

object Test {

  /** This is the main tool for making tests.
    *
    * The syntax is "java -jar JARNAME.jar options
    * Every option not included is set to default value. The options are:
    *
    * @ "-i INPUTFOLDER" for the input folder
    * @ "-o OUTPUTFOLDER" for the output folder
    * @ "-h HARNESSESFOLDER" for the harnesses folder
    * @ "-r REPETITIONS" for the number of repetitions per ontology and reasoner (0 means it is done once)
    * @ "-y REASONER1 REASONER2 ... " for using only particular reasoners. This requires that individual harnesses are in the HarnessesFolder with the name used in this option.
    *
    * Other options are ("loadtest" for a load only test, "nohash" to do no hash, "nowrite" to not write taxonomy, "debug" for extra information on the terminal.)
    *
    */

  def main(args: Array[String]): Unit = {

    // Process Input //

    val inputFolder: java.io.File = getInputFolder(args).getOrElse(new java.io.File(oxfordcorpus))
    val outputFolder: java.io.File = getOutputFolder(args).getOrElse(new java.io.File(outputs))
    val harnessesFolder: java.io.File = getHarnessesFolder(args).getOrElse(new java.io.File(harnesses))
    val repetitions: Int = getRepetitions(args).getOrElse(0); assert(repetitions >= 0)
    val reasoners: List[String] = getReasoners(args, harnessesFolder.toString())
    val loadOnly: Boolean = isLoadOnly(args)
    val hashTaxonomy: Boolean = isHashTaxonomy(args)
    val writeTaxonomy: Boolean = isSaveTaxonomy(args)
    val debug: Boolean = isDebug(args)
    System.out.println("[INFO]. Testing parameters: ")
    System.out.println("   ** Input folder: " + inputFolder.toString)
    System.out.println("   ** Output folder: " + outputFolder.toString)
    System.out.println("   ** Harnesses folder: " + harnessesFolder.toString)
    System.out.println("   ** Active reasoners: " + (reasoners mkString " "))
    System.out.println("   ** Repetitions per cycle: " + repetitions)
    System.out.println("   ** Load Only Test?: " + yesno(loadOnly))
    System.out.println("   ** Hash Taxonomy?: " + yesno(hashTaxonomy))
    System.out.println("   ** Write Taxonomy?: " + yesno(writeTaxonomy))
    System.out.println("   ** Debugging?: " + yesno(debug))
    val testDate: String = {
      val date = java.util.Calendar.getInstance()
      date.get(java.util.Calendar.YEAR) + "-" +
        (date.get(java.util.Calendar.MONTH)+1) + "-" +
      date.get(java.util.Calendar.DAY_OF_MONTH) + "-" +
      date.get(java.util.Calendar.HOUR_OF_DAY) + "-" +
      date.get(java.util.Calendar.MINUTE) + "-" +
      date.get(java.util.Calendar.SECOND) + "-"
    }
    val outputFile: java.io.File = new java.io.File(outputFolder, testDate + "results.txt")
    outputFile.createNewFile

    // Iterate over each ontology //

    for (file <- inputFolder.listFiles(); if file.toString.endsWith(".owl")) {
      System.out.println("[INFO]" + "." + "Processing file" + "." + file.toString)

      // Iterate over each reasoner //

      for (reasoner <- reasoners) {

        System.out.println("[INFO]" + "." + "Classifying using" + "." + reasoner.toString)

        // Open writer to output file //
        val outputBuffer: java.io.BufferedWriter = new java.io.BufferedWriter(new java.io.FileWriter(outputFile, true))

        // Preliminary test //
        if (debug) System.out.println("[DEBUG].Starting preliminary test")
        val result = classify(file, reasoner, loadOnly, hashTaxonomy, writeTaxonomy, outputFolder.toString, debug)
        System.out.println(result.toString)
        log(file, reasoner, outputBuffer, result.toString)

        // Timed rounds //
        if (result.hasSucceeded && (repetitions > 0) ) {
          val secondResult = reClassify(file, reasoner, (repetitions - 1), 0, outputFolder.toString, debug)
          if (secondResult.startsWith("[SUCCESS].")) {
            val time = (secondResult.drop(29).toInt)/repetitions
            System.out.println("[INFO]" + "." + "Average time: " + time)
            log(file, reasoner, outputBuffer, time.toString)
          }
          else {
            System.out.println(secondResult)
            log(file, reasoner, outputBuffer, secondResult)
          }
        } // End Timed Rounds

        outputBuffer.close()
      } // End Reasoner Iteration //
    } // End Ontology Iteration //

    // Test complete //
    System.out.println("[INFO].Test Complete")

  }

  def yesno(boolean: Boolean): String =  if (boolean) return "yes" ; else return "no"

}
