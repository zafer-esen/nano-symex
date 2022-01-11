object Util {
  class Timer {
    private var stopped = true
    private var startTime : Double = System.nanoTime()
    private var stopDuration  : Double = 0

    def stop()  { stopped = true; stopDuration = System.nanoTime() - startTime }
    def start() { stopped = false; startTime = System.nanoTime() }

    def s  : Double = ns / 1e9d
    def ms : Double = ns / 1e6d
    def us : Double = ns / 1e3d
    def ns : Double =
      if (stopped) stopDuration else System.nanoTime() - startTime
  }
}
