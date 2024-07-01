
class TestResult(success: String = "", hash: String = "", time: String = "", message: String = "", contextCount: Int = 0) {

  override def toString: String = { success + " , " + hash + " , " + time + " , " + message + " , " + contextCount}

  def hasSucceeded: Boolean = {success == "[SUCCESS]"}
}
