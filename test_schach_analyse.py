import os
import time
import unittest
from types import SimpleNamespace
from unittest.mock import Mock

import schach_analyse as chess


class FakeCanvas:
    def delete(self, tag):
        pass

    def winfo_rootx(self):
        return 0

    def winfo_rooty(self):
        return 0


class FakeLabel:
    def configure(self, **kwargs):
        pass


class FakeWorker:
    def __init__(self):
        self.jobs = []

    def analyze(self, board, white):
        job = len(self.jobs) + 1
        self.jobs.append((job, board[:], white))
        return job


class EngineWorkerTests(unittest.TestCase):
    def test_drag_during_search_commits_move_and_submits_new_snapshot(self):
        app = chess.App.__new__(chess.App)
        app.cv = FakeCanvas()
        app.b = chess.START[:]
        app.drag = 52
        app.moved = True
        app.drag_piece = "P"
        app.tool = None
        app.press_xy = (0, 0)
        app.flip = False
        app.side = "w"
        app.training = False
        app.train_txt = ""
        app.best = None
        app.mate = None
        app.job = 0
        app.worker = FakeWorker()
        app.lbl_best = FakeLabel()
        app.lbl_mate = FakeLabel()
        app.btn_train = FakeLabel()
        app.memory_stats = {"matts": 0, "patterns": {}}
        app.draw = Mock()
        app.update_learn = Mock()

        app._release(SimpleNamespace(x_root=348, y_root=348))

        self.assertEqual(app.b[52], ".")
        self.assertEqual(app.b[36], "P")
        self.assertEqual(app.worker.jobs, [(1, app.b[:], True)])

    def test_stale_analysis_result_is_ignored(self):
        app = chess.App.__new__(chess.App)
        app.job = 4
        app.show_mate = Mock()
        app.show_result = Mock()

        app._handle_worker_message(
            ("analysis", 3, None, None, None, {"matts": 0, "patterns": {}})
        )

        app.show_mate.assert_not_called()
        app.show_result.assert_not_called()

    def test_process_cancels_old_work_and_accepts_new_position(self):
        worker = chess.EngineWorker()
        try:
            deadline = time.monotonic() + 10
            while time.monotonic() < deadline:
                message = worker.poll()
                if message and message[0] == "memory":
                    break
                time.sleep(0.01)
            else:
                self.fail("Engine process did not initialize")

            old_job = worker.analyze(chess.START, True)
            self.assertNotEqual(worker.process.pid, os.getpid())
            time.sleep(0.1)
            training_job = worker.train()
            time.sleep(0.1)
            latest_job = worker.analyze(["."] * 64, True)
            self.assertGreater(training_job, old_job)

            heartbeat = 0
            result = None
            deadline = time.monotonic() + 10
            while time.monotonic() < deadline:
                heartbeat += 1
                message = worker.poll()
                if message and message[0] == "analysis" and message[1] == latest_job:
                    result = message
                    break
                time.sleep(0.01)

            self.assertIsNotNone(result, "Latest analysis was not returned")
            self.assertGreater(heartbeat, 1)
            self.assertIsNone(result[4])
        finally:
            worker.close()


if __name__ == "__main__":
    unittest.main()
