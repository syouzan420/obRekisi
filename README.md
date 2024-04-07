# rekisi

やったこと
/etc/nixos/configuration.nix
で
```
nix.settings.substituters = [ "https://nixcache.reflex-frp.org" ];
nix.settings.trusted-public-keys = [ "ryantrinkle.com-1:JJiAKaRv9mWgpVAz8dwewnZe0AzzEAzPkagE9SP5NWI=" ];
nix.settings.experimental-features = [ "nix-command" ];
```
を追加
```
sudo -i nixos-rebuild switch --upgrade
```
で 變更を反映させる

フォルダをつくり
その中で
```
ob init
```
を實行

