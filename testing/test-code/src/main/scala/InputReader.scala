package test

object InputReader {

  def getInputFolder(args: Array[String]): Option[java.io.File] = {
    for (i <- 0 until args.length; if (args(i) == "-i")) {
      try {
        val inputFolder: java.io.File = new java.io.File(args(i + 1))
        assert(inputFolder.isDirectory)
        return Some(inputFolder)
      }
      catch {
        case e: NullPointerException => {
          System.err.println("Expected argument after -i : input folder.")
          return None
        }
        case e: Exception => {
          System.err.println(args(i + 1) + " is not a valid input folder.")
          e.printStackTrace 
          return None
        }
      }
    }
    return None
  }

  def getOutputFolder(args: Array[String]): Option[java.io.File] = {
    for (i <- 0 until args.length; if (args(i) == "-o")) {
      try {
       val outputFolder: java.io.File = new java.io.File(args(i + 1))
        assert(outputFolder.isDirectory)
        return Some(outputFolder)
      }
      catch {
        case e: NullPointerException => {
          System.err.println("Expected argument after -o : output folder.")
          return None
        }
        case _: Exception => {
          System.err.println(args(i + 1) + " is not a valid output folder.")
          return None
        }
      }
    }
    return None
  }

  def getHarnessesFolder(args: Array[String]): Option[java.io.File] = {
    for (i <- 0 until args.length; if (args(i) == "-h")) {
      try {
        val harnessesFolder: java.io.File = new java.io.File(args(i + 1))
        assert(harnessesFolder.isDirectory)
        return Some(harnessesFolder)
      }
      catch {
        case e: NullPointerException => {
          System.err.println("Expected argument after -h : harnesses folder.")
          return None
        }
        case _: Exception => {
          System.err.println(args(i + 1) + " is not a valid harnesses folder.")
          return None
        }
      }
    }
    return None
  }

  def getRepetitions(args: Array[String]): Option[Int] = {
    for (i <- 0 to args.length - 1; if (args(i) == "-r")) {
      try {
        val repetitions: Int = args(i + 1).toInt
        return Some(repetitions)
      }
      catch {
        case e: NullPointerException => {
          System.err.println("Expected argument after -r : number of repetitons per cycle.")
          return None
        }
        case e: Exception => {
          System.err.println(args(i + 1) + " is not a valid number of repetitions per cycle.")
          return None
        }
      }
    }
    return None
  }

   def getReasoners(args: Array[String], harnessesFolder: String): List[String] = {

     val reasoners = scala.collection.mutable.MutableList[String]()

     // CASE 1: check if reasoners have been specified; pick those
     for (arg <- args) {
       try {
         arg match {
           case "jcel"|"elk"|"factpp"|"hermit"|"konclude"|"pellet"|"sequoia-affinis"|"sequoia-chinensis"|"snorocket"|"sequoia-affinis-multi" =>  {
             reasoners += (harnessesFolder + "/" + arg + ".jar")
           }
           case _ => 
         }
       }
       catch {
         case _ : Throwable =>
       }
     }
     if (!reasoners.isEmpty) return reasoners.toList

     // CASE 2: reasoners have not been specified; pick all in the folder
     try {
       for (reasoner <- (new java.io.File(harnessesFolder)).listFiles() ) {
         if (reasoner.toString.endsWith(".jar")) reasoners += reasoner.toString
       }
     }
     catch {
       case _: Throwable =>
     }
     return reasoners.toList

   }



  def isLoadOnly(args: Array[String]): Boolean = args.exists( arg => arg == "loadtest")

  def isDebug(args: Array[String]): Boolean = args.exists( arg => arg == "debug")

  def isHashTaxonomy(args: Array[String]): Boolean = args.forall( arg => arg != "nohash")

  def isSaveTaxonomy(args: Array[String]): Boolean = args.forall( arg => arg != "nowrite")

}

