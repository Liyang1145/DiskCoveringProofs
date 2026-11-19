from candidate import replay_main
from network import replay_networks
from radial import replay_radial


if __name__ == '__main__':
    if not __debug__:
        raise RuntimeError('This checker uses assertions. Run without -O.')
    replay_main()
    replay_networks()
    replay_radial()
    print('All exact checks passed.')
