import json
import numpy as np

# this is essentially a customized openai-gym interface,
# extended with aptly named convenience methods...
class Environment():
    def step(self, action):
        raise NotImplementedError()

    def reset(self):
        raise NotImplementedError()

    def get_n_actions(self):
        raise NotImplementedError()

    def get_n_states(self):
        raise NotImplementedError()


class Outcome():
    def __init__(self, n_episodes, policy, V, Q):
        self.n_episodes = n_episodes
        self.policy = policy
        self.V = V
        self.Q = Q

    def get_n_episodes(self):
        return self.n_episodes

    def to_json(self):
        return json.dumps(dict(
            type=self.__class__.__name__,
            n_episodes=self.n_episodes,
            policy=self.policy.tolist(),
            V=self.V.tolist(),
            Q=self.Q.tolist(),
        ))

    @staticmethod
    def from_json(jsonstring):
        data = json.loads(jsonstring)
        return Outcome(
            data['n_episodes'],
            np.array(data['policy']),
            np.array(data['V']),
            np.array(data['Q'])
        )


def get_flat_policy(env, policy):
    flat_policy = []
    for state in range(env.get_n_states()):
        for action in range(env.get_n_actions()):
            flat_policy.append((state, action, policy[state, action]))
    return flat_policy
