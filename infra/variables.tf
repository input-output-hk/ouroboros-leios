variable "repository" {
  type        = string
  description = "The repository to pull the image from"
  default     = "ghcr.io/input-output-hk"
}

variable "image" {
  type        = string
  description = "The image to pull"
  default     = "ouroboros-leios"
}

variable "tag" {
  type        = string
  description = "The tag to pull"
  default     = "latest"
}

variable "ghcr-pat" {
  type        = string
  description = "The Personal Access Token to use to pull the image"
}
