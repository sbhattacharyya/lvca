from pygame import mixer
import pygame
import sys

if len(sys.argv) == 2:
    filename = sys.argv[1]

    mixer.init()
    pygame.init()
    mixer.music.set_endevent(1)

    f = open(filename, 'w+b')
    mixer.music.load(f)
    mixer.music.play()
    pygame.event.wait()
    f.close()
