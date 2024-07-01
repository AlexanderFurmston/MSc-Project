

object Addresses {

  private var ROOT: String = "/home/davala/sequoia-tests/"
  private val OXFORD_CORPUS: String = "data/oxfordcorpus"
  private val GARBAGE_OUTPUT: String = "outputs/"
  private val INPUTS: String = ROOT + "data/"
  private val TAXONOMIES: String = ROOT + "outputs/taxonomies/"
  private val OUTPUTS: String = ROOT + "outputs/"
  private val HARNESSES: String = ROOT + "harnesses/"
  private val HARNESS_ELK: String = HARNESSES + "elk.jar"
  private val HARNESS_JCEL: String = HARNESSES + "jcel.jar"
  private val HARNESS_KONCLUDE: String = HARNESSES + "konclude.jar"
  private val HARNESS_HERMIT: String = HARNESSES + "hermit.jar"
  private val HARNESS_FACTPP: String = HARNESSES + "factpp.jar"
  private val HARNESS_PELLET: String = HARNESSES + "pellet.jar"
  private val HARNESS_SEQUOIA_AFFINIS: String = HARNESSES + "sequoia-affinis.jar"
  private val HARNESS_SEQUOIA_CHINENSIS: String = HARNESSES + "sequoia-chinensis.jar"
  private val HARNESS_SNOROCKET: String = HARNESSES + "snorocket.jar"

  def sequoiaAffinis: String = HARNESS_SEQUOIA_AFFINIS
  def sequoiaChinensis: String = HARNESS_SEQUOIA_CHINENSIS
  def inputs: String = INPUTS
  def outputs: String = OUTPUTS
  def taxonomies: String = TAXONOMIES
  def oxfordcorpus: String = OXFORD_CORPUS
  def harnesses: String = HARNESSES
  def sequoiaC: String = HARNESS_SEQUOIA_CHINENSIS
  // TODO: Add setters and getteris


}

