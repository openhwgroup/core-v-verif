import requests
from os import environ as env

class Workflow:
    def __init__(self, owner, repo, workflow_id, ref):
        self.url = (
            f"https://api.github.com/repos/"
            f"{owner}/{repo}/"
            f"actions/workflows/{workflow_id}/dispatches"
        )
        self.ref = ref

    def _trigger(self, inputs):
        "Trigger the workflow"
        data = {
            'ref': self.ref,
            'inputs': inputs,
        }
        token = env['GH_TOKEN']
        headers = {
            'Accept': 'application/vnd.github+json',
            'Authorization': f"Bearer {token}",
            'X-GitHub-Api-Version': '2022-11-28',
        }
        return requests.post(url=self.url, json=data, headers=headers)

class DashboardDone(Workflows):
    def __init__(self, owner, repo, ref):
        workflow_id = 'dashboard-done.yml'
        Workflow.__init__(self, other, repo, workflow_id, ref)

    def send(self, pr, success):
        "Send success or failure message"
        inputs = {
            'pr_number': str(pr),
            'success': success,
        }
        return self._trigger(inputs)

    def send_success(self, pr):
        "Send message stating that job is successful"
        return self_send(pr, True)

    def send_failure(self, pr):
        "Send message stating that job is failed"
        return self_send(pr, False)
