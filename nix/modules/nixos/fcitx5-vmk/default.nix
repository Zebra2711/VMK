{
  config,
  lib,
  inputs,
  pkgs,
  ...
}:
with lib; let
  cfg = config.services.fcitx5-vmk;
  fcitx5-vmk = inputs.self.packages.${pkgs.stdenv.hostPlatform.system}.fcitx5-vmk;
in {
  options.services.fcitx5-vmk = {
    enable = mkEnableOption "Fcitx5 VMK Server";
    user = mkOption {
      type = types.str;
      default = "";
    };
  };

  config = mkIf cfg.enable {
    i18n.inputMethod.fcitx5.addons = [fcitx5-vmk];

    users.users.uinput_proxy = {
      isSystemUser = true;
      group = "input";
    };

    services.udev.packages = [fcitx5-vmk];
    systemd.packages = [fcitx5-vmk];

    systemd.targets.multi-user.wants = ["fcitx5-vmk-server@${cfg.user}.service"];
  };
}
